// Postgres wire protocol v3 client. Connection setup (startup, SCRAM-SHA-256, Parse of every statement) is
// blocking and runs once per connection at boot. After that a connection is driven by the worker's io_uring:
// each request appends one batch (Bind+Execute per statement, then one Sync) and batches are pipelined, so
// one connection carries many requests' queries without waiting for each reply. A batch's statements run in
// one implicit transaction that commits at its Sync; the reply is the ReadyForQuery after it.
#include "conduit.h"
#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/random.h>
#include <sys/socket.h>
#include <unistd.h>

static inline void put32(buf_t *b, uint32_t v) {
    uint8_t x[4] = {v >> 24, v >> 16, v >> 8, v};
    buf_put(b, x, 4);
}
static inline void put16(buf_t *b, uint16_t v) {
    uint8_t x[2] = {v >> 8, v};
    buf_put(b, x, 2);
}
static inline uint32_t get32(const char *p) {
    const uint8_t *u = (const uint8_t *)p;
    return (uint32_t)u[0] << 24 | (uint32_t)u[1] << 16 | (uint32_t)u[2] << 8 | u[3];
}
static inline uint16_t get16(const char *p) {
    const uint8_t *u = (const uint8_t *)p;
    return (uint16_t)(u[0] << 8 | u[1]);
}
// Patches the length of the message that starts (at its type byte) at offset `at`.
static inline void fix_len(buf_t *b, size_t at) {
    uint32_t n = b->len - at - 1;
    uint8_t *p = (uint8_t *)b->p + at + 1;
    p[0] = n >> 24; p[1] = n >> 16; p[2] = n >> 8; p[3] = n;
}

// ---------- blocking setup ----------

static void write_all(int fd, const void *p, size_t n) {
    while (n) {
        ssize_t k = write(fd, p, n);
        if (k < 0) {
            if (errno == EINTR) continue;
            die("postgres write: %s", strerror(errno));
        }
        p = (const char *)p + k;
        n -= k;
    }
}

static void read_all(int fd, void *p, size_t n) {
    while (n) {
        ssize_t k = read(fd, p, n);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) die("postgres read: %s", k ? strerror(errno) : "connection closed");
        p = (char *)p + k;
        n -= k;
    }
}

// Reads one message; returns its type, body in *b (reused).
static char read_msg(int fd, buf_t *b) {
    char h[5];
    read_all(fd, h, 5);
    uint32_t len = get32(h + 1);
    if (len < 4) die("postgres: bad message length");
    b->len = 0;
    if (b->cap < len) buf_grow(b, len);
    read_all(fd, b->p, len - 4);
    b->len = len - 4;
    return h[0];
}

static const char *err_field(const buf_t *b, char f) {
    for (size_t i = 0; i < b->len && b->p[i];) {
        char t = b->p[i];
        const char *v = b->p + i + 1;
        if (t == f) return v;
        i += 2 + strlen(v);
    }
    return "";
}

static void send_pw_msg(int fd, const char *data, size_t n) {
    buf_t m = {0};
    buf_putc(&m, 'p');
    put32(&m, 0);
    buf_put(&m, data, n);
    fix_len(&m, 0);
    write_all(fd, m.p, m.len);
    buf_free(&m);
}

static const char *scram_attr(const char *msg, char key, size_t *len) {
    for (const char *p = msg; *p;) {
        const char *e = strchr(p, ',');
        if (!e) e = p + strlen(p);
        if (p[0] == key && p[1] == '=') {
            *len = e - p - 2;
            return p + 2;
        }
        p = *e ? e + 1 : e;
    }
    return NULL;
}

static void scram_auth(int fd, buf_t *b) {
    uint8_t rnd[18];
    if (getrandom(rnd, sizeof rnd, 0) != sizeof rnd) die("getrandom failed");
    char cnonce[32];
    cnonce[b64_enc(cnonce, rnd, sizeof rnd)] = 0;
    char first_bare[64];
    snprintf(first_bare, sizeof first_bare, "n=,r=%s", cnonce);
    char first[80];
    int fl = snprintf(first, sizeof first, "n,,%s", first_bare);

    buf_t m = {0};
    buf_putc(&m, 'p');
    put32(&m, 0);
    buf_put(&m, "SCRAM-SHA-256", 14);
    put32(&m, fl);
    buf_put(&m, first, fl);
    fix_len(&m, 0);
    write_all(fd, m.p, m.len);
    buf_free(&m);

    char t = read_msg(fd, b);
    if (t == 'E') die("postgres auth: %s", err_field(b, 'M'));
    if (t != 'R' || b->len < 4 || get32(b->p) != 11) die("postgres auth: expected SASLContinue");
    char server_first[512];
    size_t sl = b->len - 4 < sizeof server_first - 1 ? b->len - 4 : sizeof server_first - 1;
    memcpy(server_first, b->p + 4, sl);
    server_first[sl] = 0;

    size_t rl, sl2, il;
    const char *r = scram_attr(server_first, 'r', &rl);
    const char *s = scram_attr(server_first, 's', &sl2);
    const char *it = scram_attr(server_first, 'i', &il);
    if (!r || !s || !it || rl < strlen(cnonce) || memcmp(r, cnonce, strlen(cnonce)) != 0) die("postgres auth: bad SCRAM challenge");
    uint8_t salt[128];
    long saltn = b64_dec(salt, s, sl2);
    if (saltn < 0 || saltn > 120) die("postgres auth: bad SCRAM salt");
    int iters = atoi(it);
    if (iters <= 0) die("postgres auth: bad SCRAM iteration count");

    // SaltedPassword = Hi(password, salt, i) (PBKDF2-HMAC-SHA256, one block)
    const char *pw = CFG.db_pass;
    hmac_key_t pk;
    hmac_key_init(&pk, pw, strlen(pw));
    uint8_t u[32], salted[32];
    memcpy(salt + saltn, "\0\0\0\1", 4);
    hmac_sha256_k(&pk, salt, saltn + 4, u);
    memcpy(salted, u, 32);
    for (int i = 1; i < iters; i++) {
        hmac_sha256_k(&pk, u, 32, u);
        for (int k = 0; k < 32; k++) salted[k] ^= u[k];
    }
    uint8_t ckey[32], skey[32], csig[32], proof[32];
    hmac_sha256(salted, 32, "Client Key", 10, ckey);
    sha256_t sh;
    sha256_init(&sh);
    sha256_update(&sh, ckey, 32);
    sha256_final(&sh, skey);

    char final_wo[512];
    int fwl = snprintf(final_wo, sizeof final_wo, "c=biws,r=%.*s", (int)rl, r);
    buf_t am = {0};
    buf_put(&am, first_bare, strlen(first_bare));
    buf_putc(&am, ',');
    buf_put(&am, server_first, strlen(server_first));
    buf_putc(&am, ',');
    buf_put(&am, final_wo, fwl);
    hmac_sha256(skey, 32, am.p, am.len, csig);
    buf_free(&am);
    for (int k = 0; k < 32; k++) proof[k] = ckey[k] ^ csig[k];
    char final[640];
    int n = snprintf(final, sizeof final, "%s,p=", final_wo);
    n += b64_enc(final + n, proof, 32);
    send_pw_msg(fd, final, n);

    t = read_msg(fd, b);
    if (t == 'E') die("postgres auth: %s", err_field(b, 'M'));
    if (t != 'R' || get32(b->p) != 12) die("postgres auth: expected SASLFinal");
}

static int dial(void) {
    struct addrinfo hints = {.ai_family = AF_UNSPEC, .ai_socktype = SOCK_STREAM}, *res;
    int e = getaddrinfo(CFG.db_host, CFG.db_port, &hints, &res);
    if (e) die("postgres address %s:%s: %s", CFG.db_host, CFG.db_port, gai_strerror(e));
    int fd = -1;
    for (struct addrinfo *ai = res; ai; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype | SOCK_CLOEXEC, ai->ai_protocol);
        if (fd < 0) continue;
        if (connect(fd, ai->ai_addr, ai->ai_addrlen) == 0) break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) die("connect to postgres %s:%s: %s", CFG.db_host, CFG.db_port, strerror(errno));
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    return fd;
}

static void startup_param(buf_t *m, const char *k, const char *v) {
    buf_put(m, k, strlen(k) + 1);
    buf_put(m, v, strlen(v) + 1);
}

void pg_connect(pgconn_t *c, worker_t *w) {
    memset(c, 0, sizeof *c);
    c->w = w;
    c->fd = dial();
    int fd = c->fd;

    buf_t m = {0};
    put32(&m, 0);
    put32(&m, 196608); // protocol 3.0
    startup_param(&m, "user", CFG.db_user);
    startup_param(&m, "database", CFG.db_name);
    startup_param(&m, "client_encoding", "UTF8");
    startup_param(&m, "DateStyle", "ISO, MDY");
    startup_param(&m, "TimeZone", "UTC");
    startup_param(&m, "application_name", "conduit-c-iouring");
    // Session-level settings for our own connections (allowed by the rules, unlike server-wide changes).
    char *opts = strdup(CFG.pg_session), *save = NULL;
    for (char *kv = strtok_r(opts, ",", &save); kv; kv = strtok_r(NULL, ",", &save)) {
        char *eq = strchr(kv, '=');
        if (!eq) die("PG_SESSION entries must look like name=value, got %s", kv);
        *eq = 0;
        startup_param(&m, kv, eq + 1);
    }
    free(opts);
    buf_putc(&m, 0);
    uint32_t n = m.len;
    uint8_t *p = (uint8_t *)m.p;
    p[0] = n >> 24; p[1] = n >> 16; p[2] = n >> 8; p[3] = n;
    write_all(fd, m.p, m.len);

    buf_t b = {0};
    for (;;) {
        char t = read_msg(fd, &b);
        if (t == 'E') die("postgres: %s", err_field(&b, 'M'));
        if (t == 'R') {
            uint32_t code = get32(b.p);
            if (code == 0) continue;
            if (code == 3) { send_pw_msg(fd, CFG.db_pass, strlen(CFG.db_pass) + 1); continue; }
            if (code == 10) { scram_auth(fd, &b); continue; }
            die("postgres: unsupported auth method %u (use scram-sha-256, password or trust)", code);
        }
        if (t == 'Z') break;
    }

    // Prepare every statement once on this connection.
    m.len = 0;
    for (int i = 0; i < NSTMTS; i++) {
        size_t at = m.len;
        buf_putc(&m, 'P');
        put32(&m, 0);
        char name[16];
        int nl = snprintf(name, sizeof name, "s%d", i);
        buf_put(&m, name, nl + 1);
        buf_put(&m, STMTS[i].sql, strlen(STMTS[i].sql) + 1);
        put16(&m, STMTS[i].nparams);
        for (int k = 0; k < STMTS[i].nparams; k++) put32(&m, STMTS[i].oids[k]);
        fix_len(&m, at);
    }
    buf_putc(&m, 'S');
    put32(&m, 4);
    write_all(fd, m.p, m.len);
    int parsed = 0;
    for (;;) {
        char t = read_msg(fd, &b);
        if (t == 'E') die("postgres: preparing statement s%d: %s", parsed, err_field(&b, 'M'));
        if (t == '1') parsed++;
        if (t == 'Z') break;
    }
    buf_free(&m);
    buf_free(&b);
}

// ---------- pipelined batches ----------

static const char SYNC[5] = {'S', 0, 0, 0, 4};

static pgconn_t *pg_choose_conn(worker_t *w) {
    if (w->wq_head) return NULL;
    pgconn_t *best = &w->pg[0];
    for (int i = 1; i < w->npg; i++)
        if (w->pg[i].inflight < best->inflight) best = &w->pg[i];
    return best->inflight < CFG.pg_depth ? best : NULL;
}

// A connection carries at most CFG.pg_depth batches at a time; the rest wait in the worker's FIFO queue and go
// out, oldest first, as replies free slots. A batch built while a connection has room (and nothing is queued)
// is written straight into that connection's output buffer; otherwise into its own buffer until it is placed.
pgbatch_t *pg_begin(req_t *r, void (*cb)(req_t *, pgbatch_t *)) {
    worker_t *w = r->w;
    pgbatch_t *b = arena_alloc(&r->arena, sizeof *b);
    memset(b, 0, sizeof *b);
    b->req = r;
    b->cb = cb;
    b->buf = &b->own;
    pgconn_t *c = pg_choose_conn(w);
    if (c) {
        b->conn = c;
        b->buf = &c->out;
    }
    return b;
}

void pg_stmt(pgbatch_t *b, int stmt, const str_t *params) {
    buf_t *o = b->buf;
    const stmt_def_t *d = &STMTS[stmt];
    size_t at = o->len;
    buf_putc(o, 'B');
    put32(o, 0);
    buf_putc(o, 0); // unnamed portal
    char name[16];
    int nl = snprintf(name, sizeof name, "s%d", stmt);
    buf_put(o, name, nl + 1);
    put16(o, 0); // all parameters in text format
    put16(o, d->nparams);
    for (int i = 0; i < d->nparams; i++) {
        if (!params[i].p) {
            put32(o, 0xFFFFFFFFu);
        } else {
            put32(o, params[i].n);
            buf_put(o, params[i].p, params[i].n);
        }
    }
    put16(o, 0); // all results in text format
    fix_len(o, at);
    static const char exec[10] = {'E', 0, 0, 0, 9, 0, 0, 0, 0, 0};
    buf_put(o, exec, sizeof exec);
    b->nst++;
    if (UNLIKELY(STATS_ON) && stmt_is_write(stmt)) b->is_write = true;
}

static void pg_link(pgconn_t *c, pgbatch_t *b) {
    b->conn = c;
    if (c->tail) c->tail->next = b;
    else c->head = b;
    c->tail = b;
    c->inflight++;
    if (UNLIKELY(STATS_ON)) stats_pg_enq(c, b);
}

static void pg_queue_batch(worker_t *w, pgbatch_t *b) {
    buf_put(b->buf, SYNC, sizeof SYNC);
    if (UNLIKELY(STATS_ON)) b->t_enq = stats_now();
    if (b->conn) {
        pg_link(b->conn, b);
        return;
    }
    b->next = NULL;
    if (w->wq_tail) w->wq_tail->next = b;
    else w->wq_head = b;
    w->wq_tail = b;
    w->wq_n++;
}

void pg_end(pgbatch_t *b) {
    pg_queue_batch(b->req->w, b);
}

// ---------- cross-request batched statements ----------

static void pg_carrier_done(req_t *r, pgbatch_t *b);
static void pg_flush_pool(worker_t *w, int stmt);

static void buf_pg_array_elem(buf_t *b, str_t s) {
    if (!s.p) {
        buf_lit(b, "NULL");
        return;
    }
    buf_putc(b, '"');
    for (size_t i = 0; i < s.n; i++) {
        char c = s.p[i];
        if (c == '"' || c == '\\') buf_putc(b, '\\');
        buf_putc(b, c);
    }
    buf_putc(b, '"');
}

static void pg_flush_pool(worker_t *w, int stmt) {
    if (!w->pools) return;
    pgpool_t *pool = &w->pools[stmt];
    int nparams = STMTS[stmt].nparams;
    while (pool->head && pool->inflight < CFG.batch_hold) {
        int count = pool->count < CFG.batch_max ? pool->count : CFG.batch_max;
        pgbatch_t **members = malloc(count * sizeof *members);
        if (!members) die("out of memory");
        for (int i = 0; i < count; i++) {
            pgbatch_t *m = pool->head;
            pool->head = m->qnext;
            if (!pool->head) pool->tail = NULL;
            pool->count--;
            m->qnext = NULL;
            members[i] = m;
        }
        pool->inflight++;

        pgbatch_t *carrier = calloc(1, sizeof *carrier);
        if (!carrier) die("out of memory");
        carrier->cb = pg_carrier_done;
        carrier->is_carrier = true;
        carrier->stmt = stmt;
        carrier->w = w;
        carrier->nmembers = count;
        carrier->members = members;
        carrier->buf = &carrier->own;

        pgconn_t *c = pg_choose_conn(w);
        if (c) {
            carrier->conn = c;
            carrier->buf = &c->out;
        }

        buf_t abufs[nparams > 0 ? nparams : 1];
        str_t aparams[nparams > 0 ? nparams : 1];
        for (int j = 0; j < nparams; j++) {
            abufs[j] = (buf_t){0};
            buf_putc(&abufs[j], '{');
            for (int i = 0; i < count; i++) {
                if (i > 0) buf_putc(&abufs[j], ',');
                buf_pg_array_elem(&abufs[j], members[i]->params[j]);
            }
            buf_putc(&abufs[j], '}');
            aparams[j] = (str_t){abufs[j].p, abufs[j].len};
        }

        pg_stmt(carrier, stmt, aparams);
        for (int j = 0; j < nparams; j++) buf_free(&abufs[j]);

        pg_queue_batch(w, carrier);
    }
}

static void pg_carrier_done(req_t *r, pgbatch_t *b) {
    (void)r;
    worker_t *w = b->w;
    int stmt = b->stmt;
    for (int i = 0; i < b->nmembers; i++) {
        pgbatch_t *m = b->members[i];
        m->conn = b->conn;
        m->failed = b->failed;
        memcpy(m->sqlstate, b->sqlstate, sizeof m->sqlstate);
        m->cur = b->cur;
        m->cb(m->req, m);
    }
    free(b->members);
    buf_free(&b->own);
    free(b);

    if (w->pools) {
        pgpool_t *pool = &w->pools[stmt];
        pool->inflight--;
        pg_flush_pool(w, stmt);
    }
}

void pg_batched(req_t *r, int stmt, const str_t *params, void (*cb)(req_t *, pgbatch_t *)) {
    worker_t *w = r->w;
    if (UNLIKELY(!w->pools)) {
        w->pools = calloc(NSTMTS, sizeof *w->pools);
        if (!w->pools) die("out of memory");
    }
    pgpool_t *pool = &w->pools[stmt];

    pgbatch_t *b = arena_alloc(&r->arena, sizeof *b);
    memset(b, 0, sizeof *b);
    b->req = r;
    b->cb = cb;
    b->nst = 1;
    b->cur = 0;
    b->stmt = stmt;

    int nparams = STMTS[stmt].nparams;
    if (nparams > 0) {
        str_t *cp = arena_alloc(&r->arena, nparams * sizeof *cp);
        memcpy(cp, params, nparams * sizeof *cp);
        b->params = cp;
    }

    b->qnext = NULL;
    if (pool->tail) pool->tail->qnext = b;
    else pool->head = b;
    pool->tail = b;
    pool->count++;

    if (pool->inflight < CFG.batch_hold) pg_flush_pool(w, stmt);
}

// Moves queued batches onto `c` while it has room.
static void pg_fill(pgconn_t *c) {
    worker_t *w = c->w;
    while (w->wq_head && c->inflight < CFG.pg_depth) {
        pgbatch_t *b = w->wq_head;
        w->wq_head = b->next;
        if (!w->wq_head) w->wq_tail = NULL;
        w->wq_n--;
        b->next = NULL;
        buf_put(&c->out, b->own.p, b->own.len);
        buf_free(&b->own);
        pg_link(c, b);
    }
}

void pg_flush(pgconn_t *c) {
    if (c->send_inflight) return;
    if (c->out.len == 0) return;
    buf_t t = c->sending;
    c->sending = c->out;
    c->out = t;
    c->out.len = 0;
    c->sent = 0;
    c->send_inflight = true;
    struct io_uring_sqe *sqe = get_sqe(c->w);
    io_uring_prep_send(sqe, c->fd, c->sending.p, c->sending.len, MSG_NOSIGNAL);
    io_uring_sqe_set_data64(sqe, UD(c, UD_PGSEND));
}

void pg_on_send(pgconn_t *c, int res) {
    if (res < 0) die("postgres send: %s", strerror(-res));
    c->sent += res;
    if (c->sent < c->sending.len) {
        struct io_uring_sqe *sqe = get_sqe(c->w);
        io_uring_prep_send(sqe, c->fd, c->sending.p + c->sent, c->sending.len - c->sent, MSG_NOSIGNAL);
        io_uring_sqe_set_data64(sqe, UD(c, UD_PGSEND));
        return;
    }
    c->sending.len = 0;
    c->send_inflight = false;
    pg_flush(c);
}

void pg_arm_recv(pgconn_t *c) {
    if (c->in.cap - c->in.len < 16384) buf_grow(&c->in, 16384);
    struct io_uring_sqe *sqe = get_sqe(c->w);
    io_uring_prep_recv(sqe, c->fd, c->in.p + c->in.len, c->in.cap - c->in.len, 0);
    io_uring_sqe_set_data64(sqe, UD(c, UD_PGRECV));
}

static void pg_append_row(arena_t *a, pgst_t *st, int ncols, const char *raw_cols, size_t raw_len) {
    if (st->nrows == 0) st->ncols = ncols;
    if ((size_t)(st->nrows + 1) * (size_t)ncols > st->cap) {
        size_t cap = st->cap ? st->cap * 2 : (size_t)ncols * 4;
        while (cap < (size_t)(st->nrows + 1) * (size_t)ncols) cap *= 2;
        pgf_t *f = arena_alloc(a, cap * sizeof *f);
        if (st->f) memcpy(f, st->f, (size_t)st->nrows * (size_t)ncols * sizeof *f);
        st->f = f;
        st->cap = cap;
    }
    char *copy = arena_alloc(a, raw_len);
    memcpy(copy, raw_cols, raw_len);
    const char *p = copy;
    pgf_t *row = st->f + (size_t)st->nrows * (size_t)ncols;
    for (int i = 0; i < ncols; i++) {
        int32_t n = (int32_t)get32(p);
        p += 4;
        row[i].p = p;
        row[i].n = n;
        if (n > 0) p += n;
    }
    st->nrows++;
}

static void on_datarow(pgbatch_t *b, const char *body, uint32_t len) {
    if (b->failed) return;
    int ncols = get16(body);
    if (b->is_carrier) {
        if (ncols < 2 || len < 6) return;
        int32_t pos_len = (int32_t)get32(body + 2);
        if (pos_len <= 0 || (size_t)len < 6 + (size_t)pos_len) return;
        const char *pos_str = body + 6;
        int64_t pos;
        if (!parse_uint(pos_str, (size_t)pos_len, &pos)) return;
        if (pos < 1 || pos > (int64_t)b->nmembers) return;
        pgbatch_t *m = b->members[pos - 1];
        if (!m || m->failed) return;
        const char *p = pos_str + pos_len;
        pg_append_row(&m->req->arena, &m->st[0], ncols - 1, p, (size_t)((body + len) - p));
        return;
    }
    if (b->cur >= PG_MAXST || len < 2) return;
    pg_append_row(&b->req->arena, &b->st[b->cur], ncols, body + 2, (size_t)(len - 2));
}

void pg_on_recv(pgconn_t *c, int res) {
    if (res <= 0) die("postgres recv: %s", res ? strerror(-res) : "connection closed");
    c->in.len += res;
    size_t off = 0;
    while (c->in.len - off >= 5) {
        const char *m = c->in.p + off;
        uint32_t len = get32(m + 1);
        if (c->in.len - off < (size_t)len + 1) break;
        const char *body = m + 5;
        uint32_t blen = len - 4;
        off += len + 1;
        pgbatch_t *b = c->head;
        switch (m[0]) {
        case 'D':
            if (b) on_datarow(b, body, blen);
            break;
        case 'C':
        case 'I':
            if (b) b->cur++;
            break;
        case 'E': {
            buf_t eb = {(char *)body, blen, blen};
            const char *code = err_field(&eb, 'C');
            if (!b) die("postgres error outside a batch: %s", err_field(&eb, 'M'));
            b->failed = true;
            snprintf(b->sqlstate, sizeof b->sqlstate, "%s", code);
            if (strcmp(code, "23505") != 0) logf_("postgres error %s: %s", code, err_field(&eb, 'M'));
            break;
        }
        case 'Z':
            if (!b) die("postgres: unexpected ReadyForQuery");
            c->head = b->next;
            if (!c->head) c->tail = NULL;
            c->inflight--;
            if (UNLIKELY(STATS_ON)) stats_pg_done(c, b);
            pg_fill(c);
            b->cb(b->req, b);
            break;
        default: // BindComplete, notices, parameter status, ...
            break;
        }
    }
    if (off) {
        memmove(c->in.p, c->in.p + off, c->in.len - off);
        c->in.len -= off;
    }
    pg_arm_recv(c);
}
