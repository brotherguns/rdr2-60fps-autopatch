/* autopatch60-PPSA05813.c -- one-shot 60 fps patcher for PPSA05813.
 *
 * Waits (max. 10 min) for PPSA05813 to be the foreground app, verifies
 * both patch sites against a 64-byte context, writes, re-verifies,
 * notifies and EXITS. Nothing stays resident.
 *
 * What it patches (UE4 RHI, rhi.SyncInterval -> sceVideoOutSetFlipRate):
 *     dec ebx ; test eax,eax ; cmove ebx,eax      FF CB 85 C0 0F 44 D8
 *  -> xor ebx,ebx ; nop x5                        31 DB 90 90 90 90 90
 * i.e. the flip-rate argument is always 0 (flip every vblank = 60 Hz).
 * Two call sites (RVA 0x2AAFD10 and 0x2AD2547), both must verify before
 * anything is written. This only lifts the SyncInterval cap; it does not
 * touch t.MaxFPS / frame-rate smoothing / game-logic timing.
 *
 * Uses the same local debug-daemon protocol (127.0.0.1:744) as the
 * supplied RDR2 one-shot. The protocol constants and the MAPS record layout
 * are copied from that file and are UNTESTED on your setup -- if your
 * daemon differs, the verify step fails closed (nothing is written).
 *
 * RVAs are relative to the image base (eboot vaddr 0). */
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#define PACKET_MAGIC  0xFFAABBCCu
#define WIRE_SUCCESS  0x80000000u

#define CMD_PROC_READ      0xBDAA0002u
#define CMD_PROC_WRITE     0xBDAA0003u
#define CMD_PROC_MAPS_X    0xBDAA0004u
#define CMD_CONSOLE_NOTIFY 0xBDDD0004u
#define CMD_FG_APP         0xBDDD0006u

#define PROT_EXEC 0x4u
#define IMG_BASE_DEFAULT 0x400000u   /* fast-path guess only; MAPS is the fallback */

#define AUTOPATCH_VERSION "ppsa05813-1.0"
#define LOG_PATH "/mnt/usb0/autopatch60.log"

/* ---- patch description ------------------------------------------------ */
#define PATCH_LEN  7
#define CTX_PRE    32
#define CTX_POST   25                          /* 32 + 7 + 25 = 64 */

static const uint8_t PATCH_ORIG[PATCH_LEN] = {0xff,0xcb,0x85,0xc0,0x0f,0x44,0xd8};
static const uint8_t PATCH_NEW[PATCH_LEN]  = {0x31,0xdb,0x90,0x90,0x90,0x90,0x90};

struct site {
    uint32_t rva;
    uint8_t  pre[CTX_PRE];    /* bytes at rva-32 .. rva-1  */
    uint8_t  post[CTX_POST];  /* bytes at rva+7  .. rva+31 */
};

static const struct site SITES[] = {
    { 0x2AAFD10u,
      { 0xeb,0x27,0x03,0x31,0xc9,0x3b,0x05,0x5d,0x00,0x95,0x05,0x0f,0x95,0xc1,0xeb,0x02,
        0x31,0xc9,0x8b,0x04,0x8b,0xbb,0x03,0x00,0x00,0x00,0x83,0xf8,0x03,0x0f,0x42,0xd8 },
      { 0x41,0x39,0x5e,0x3c,0x74,0x0f,0x41,0x8b,0x7e,0x30,0x89,0xde,0xe8,0x08,0x40,0x28,
        0x03,0x41,0x89,0x5e,0x3c,0x80,0x3d,0x31,0x00 } },
    { 0x2AD2547u,
      { 0x02,0x31,0xc9,0x8b,0x04,0x8b,0xbb,0x03,0x00,0x00,0x00,0x41,0x8b,0x7d,0x30,0x4c,
        0x8b,0x75,0x88,0x4c,0x8b,0x3d,0x8f,0x2c,0x72,0x05,0x83,0xf8,0x03,0x0f,0x42,0xd8 },
      { 0x89,0xde,0xe8,0xdb,0x17,0x26,0x03,0x41,0x89,0x5d,0x3c,0x80,0x3d,0x04,0xd8,0x92,
        0x05,0x01,0x48,0x8b,0x1d,0xe9,0x08,0x98,0x05 } },
};
#define N_SITES (sizeof(SITES) / sizeof(SITES[0]))

static const char *const WANT_TITLEIDS[] = { "PPSA05813" };
#define N_WANT (sizeof(WANT_TITLEIDS) / sizeof(WANT_TITLEIDS[0]))

/* ---- logging ---------------------------------------------------------- */
static unsigned log_n = 0;
static void tlog(const char *msg) {
    FILE *f = fopen(LOG_PATH, "a");
    if (!f)
        return;
    fprintf(f, "%u %s\n", log_n++, msg);
    fclose(f);
}

static int is_want(const char *tid) {
    unsigned i;
    for (i = 0; i < N_WANT; i++)
        if (!strcmp(tid, WANT_TITLEIDS[i]))
            return 1;
    return 0;
}

/* ---- wire helpers ----------------------------------------------------- */
static int g_sock = -1;

static void put32le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
}
static void put64le(uint8_t *p, uint64_t v) {
    put32le(p, (uint32_t)v); put32le(p + 4, (uint32_t)(v >> 32));
}
static uint32_t get32le(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static uint64_t get64le(const uint8_t *p) {
    return get32le(p) | ((uint64_t)get32le(p + 4) << 32);
}

static int recvn(uint8_t *buf, size_t n) {
    size_t got = 0;
    while (got < n) {
        ssize_t r = recv(g_sock, (char *)buf + got, n - got, 0);
        if (r <= 0)
            return -1;
        got += (size_t)r;
    }
    return 0;
}
static int sendn(const uint8_t *buf, size_t n) {
    size_t sent = 0;
    while (sent < n) {
        ssize_t r = send(g_sock, (const char *)buf + sent, n - sent, 0);
        if (r <= 0)
            return -1;
        sent += (size_t)r;
    }
    return 0;
}
static int cmd(uint32_t id, const uint8_t *body, uint32_t len) {
    uint8_t h[12];
    put32le(h, PACKET_MAGIC); put32le(h + 4, id); put32le(h + 8, len);
    if (sendn(h, 12))
        return -1;
    if (len && sendn(body, len))
        return -1;
    return 0;
}
static int expect_success(void) {
    uint8_t b[4];
    if (recvn(b, 4))
        return -1;
    return get32le(b) == WIRE_SUCCESS ? 0 : -1;
}

static int connect_dbg(void) {
    struct sockaddr_in sa;
    struct timeval tv = {10, 0};
    if (g_sock >= 0) {
        close(g_sock);
        g_sock = -1;
    }
    g_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (g_sock < 0)
        return -1;
    setsockopt(g_sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(g_sock, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons(744);
    sa.sin_addr.s_addr = htonl(0x7f000001u); /* 127.0.0.1 only */
    if (connect(g_sock, (struct sockaddr *)&sa, sizeof(sa))) {
        close(g_sock);
        g_sock = -1;
        return -1;
    }
    return 0;
}

static int notify(const char *msg) {
    uint32_t len = (uint32_t)strlen(msg) + 1;
    uint8_t b[8];
    char lb[128];
    int rc;
    put32le(b, 0); put32le(b + 4, len);
    if (cmd(CMD_CONSOLE_NOTIFY, b, 8)) {
        tlog("NOTIFY_SEND_FAIL");
        return -1;
    }
    if (sendn((const uint8_t *)msg, len)) {
        tlog("NOTIFY_DATA_FAIL");
        return -1;
    }
    rc = expect_success();
    snprintf(lb, sizeof(lb), "NOTIFY rc=%d msg=%.64s", rc, msg);
    tlog(lb);
    return rc;
}

static int fg_app(uint32_t *pid, char titleid[16]) {
    uint8_t resp[140];
    if (cmd(CMD_FG_APP, NULL, 0))
        return -1;
    if (expect_success())
        return -1;
    if (recvn(resp, 140))
        return -1;
    *pid = get32le(resp);
    memcpy(titleid, resp + 4, 16);
    titleid[15] = 0;
    return 0;
}

static int proc_read(uint32_t pid, uint64_t addr, uint8_t *out, uint32_t len) {
    uint8_t b[16];
    put32le(b, pid); put64le(b + 4, addr); put32le(b + 12, len);
    if (cmd(CMD_PROC_READ, b, 16))
        return -1;
    if (expect_success())
        return -1;
    return recvn(out, len);
}

static int proc_write(uint32_t pid, uint64_t addr, const uint8_t *data, uint32_t len) {
    uint8_t b[16];
    put32le(b, pid); put64le(b + 4, addr); put32le(b + 12, len);
    if (cmd(CMD_PROC_WRITE, b, 16))
        return -1;
    if (expect_success())
        return -1;
    if (sendn(data, len))
        return -1;
    return expect_success();
}

static void *local_memmem(const void *h, size_t hlen, const void *n, size_t nlen) {
    const uint8_t *hh = h;
    size_t i;
    if (!nlen || nlen > hlen)
        return NULL;
    for (i = 0; i + nlen <= hlen; i++)
        if (!memcmp(hh + i, n, nlen))
            return (void *)(hh + i);
    return NULL;
}

/* base = start of the lowest big RX 'executable' mapping (home of .text) */
static int eboot_base(uint32_t pid, uint64_t *base) {
    uint8_t b[4], hdr[4];
    uint64_t best = 0;
    uint32_t num, i;
    put32le(b, pid);
    if (cmd(CMD_PROC_MAPS_X, b, 4))
        return -1;
    if (expect_success())
        return -1;
    if (recvn(hdr, 4))
        return -1;
    num = get32le(hdr);
    for (i = 0; i < num; i++) {
        uint8_t e[58];
        uint64_t start, end, sz;
        uint16_t prot;
        if (recvn(e, 58))
            return -1;
        start = get64le(e + 32); end = get64le(e + 40);
        sz = end - start;
        prot = (uint16_t)(e[56] | (e[57] << 8));
        if (!(prot & PROT_EXEC))
            continue;
        if (local_memmem(e, 32, "executable", 10) == NULL)
            continue;
        if (sz < 0x1000000) /* this eboot's .text is ~97 MB */
            continue;
        if (best == 0 || start < best)
            best = start;
    }
    if (!best)
        return -1;
    *base = best;
    return 0;
}

/* Read 64 bytes around a site and classify it.
 * returns: 0 = original (patchable), 1 = already patched, -1 = mismatch/read fail */
static int check_site(uint32_t pid, uint64_t base, const struct site *s) {
    uint8_t ctx[CTX_PRE + PATCH_LEN + CTX_POST];
    uint64_t target = base + s->rva;
    if (proc_read(pid, target - CTX_PRE, ctx, sizeof(ctx)))
        return -1;
    if (memcmp(ctx, s->pre, CTX_PRE) ||
        memcmp(ctx + CTX_PRE + PATCH_LEN, s->post, CTX_POST))
        return -1;
    if (!memcmp(ctx + CTX_PRE, PATCH_ORIG, PATCH_LEN))
        return 0;
    if (!memcmp(ctx + CTX_PRE, PATCH_NEW, PATCH_LEN))
        return 1;
    return -1;
}

/* verify ALL sites at this base. 0 = ok (state[] filled), -1 = not this base */
static int check_all(uint32_t pid, uint64_t base, int state[]) {
    unsigned i;
    for (i = 0; i < N_SITES; i++) {
        state[i] = check_site(pid, base, &SITES[i]);
        if (state[i] < 0)
            return -1;
    }
    return 0;
}

#define POLL_USEC 500000u
#define LIMIT     1200u            /* 1200 x 0.5 s = 10 min */

int main(void) {
    uint32_t pid = 0;
    char titleid[16] = {0};
    uint64_t base = IMG_BASE_DEFAULT;
    int state[N_SITES];
    unsigned waited, i, patched = 0;
    char lb[128];

    printf("autopatch60 v%s (one-shot): waiting for game...\n", AUTOPATCH_VERSION);
    tlog("BOOT oneshot " AUTOPATCH_VERSION);
    if (connect_dbg()) {
        tlog("CONN_FAIL");
        return 2;
    }
    tlog("CONN_OK");

    /* 1) wait for the game */
    for (waited = 0; waited < LIMIT; waited++) {
        if (fg_app(&pid, titleid))
            break;
        if (pid && is_want(titleid))
            break;
        usleep(POLL_USEC);
    }
    if (waited >= LIMIT || !pid || !is_want(titleid)) {
        tlog("TIMEOUT_NO_GAME");
        return 0;
    }
    snprintf(lb, sizeof(lb), "SPAWN pid=%u tid=%.9s", pid, titleid);
    tlog(lb);

    /* 2) resolve base: fast-path guess, then MAPS; every site must match */
    if (check_all(pid, base, state)) {
        if (eboot_base(pid, &base) || check_all(pid, base, state)) {
            tlog("NO_TARGET");
            notify("PPSA05813 60fps: target not found, not applied");
            return 3;
        }
    }
    snprintf(lb, sizeof(lb), "BASE 0x%llx pid=%u", (unsigned long long)base, pid);
    tlog(lb);

    /* 3) write only what still needs it, re-verify each */
    for (i = 0; i < N_SITES; i++) {
        uint8_t cur[PATCH_LEN];
        uint64_t target = base + SITES[i].rva;
        if (state[i] == 1) {
            tlog("SITE_ALREADY");
            continue;
        }
        if (proc_write(pid, target, PATCH_NEW, PATCH_LEN) ||
            proc_read(pid, target, cur, PATCH_LEN) ||
            memcmp(cur, PATCH_NEW, PATCH_LEN)) {
            snprintf(lb, sizeof(lb), "WRITE_FAIL site=%u", i);
            tlog(lb);
            notify("PPSA05813 60fps: write failed");
            return 5;
        }
        patched++;
    }
    snprintf(lb, sizeof(lb), "WRITE_OK patched=%u", patched);
    tlog(lb);
    notify("PPSA05813 60fps ON");
    printf("autopatch60: applied and verified, exiting.\n");
    return 0;
}
