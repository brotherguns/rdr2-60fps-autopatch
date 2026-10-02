/* autopatch60-oneshot.c -- one-shot variant of the resident daemon.
 * Waits for the RDR2 eboot (max. 10 min), verifies, writes, re-verifies,
 * notifies and EXITS. No residency: after notifying, neither process
 * nor traffic remains. Same safety: it never writes without verifying
 * (64-byte context + original bytes).
 *
 * PORT NOTE: the patch site (RVA 0x5453029 + 64-byte context) is byte-identical
 * in the supplied eboot, which carries a region table with 4 RDR2 title IDs.
 * Only the title-ID gate needed changing: it now accepts all four. */
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

#define JAO_RVA   0x5453029u            /* 0x05853029 - 0x400000 */
#define PROT_EXEC 0x4u
#define IMG_BASE_DEFAULT 0x400000u     /* base seen 100% of the time; fast-path only */

/* 64-byte context of the eboot around the target (target at +32).
 * Verified against the supplied eboot (file-offset 0x5457029 in the ELF). */
static const uint8_t JAO_CTX[64] = {
    0x89,0x04,0xe9,0x49,0xff,0xc5,0x4d,0x39,0xf5,0x0f,0x82,0xe8,0xfd,0xff,0xff,0x8b,
    0x05,0xb2,0xcf,0xd5,0x03,0x8b,0x3d,0xcc,0xd9,0xd6,0x03,0x8d,0x70,0xff,0x85,0xc0,
    0x0f,0x44,0xf0,0xe8,0x2f,0xad,0x70,0x01,0x85,0xc0,0x0f,0x88,0xac,0x10,0x00,0x00,
    0x44,0x8b,0x05,0x68,0xcf,0xd5,0x03,0x44,0x8b,0x0d,0x65,0xcf,0xd5,0x03,0x48,0x8d
};
#define JAO_CTX_OFF 32

/* USB telemetry (read back later over FTP). Nothing sensitive. */
#define LOG_PATH "/mnt/usb0/autopatch60.log"
static unsigned log_n = 0;

static void tlog(const char *msg) {
    FILE *f = fopen(LOG_PATH, "a");
    if (!f)
        return;
    fprintf(f, "%u %s\n", log_n++, msg);
    fclose(f);
}

static const uint8_t JAO_ORIG[3] = {0x0f, 0x44, 0xf0}; /* cmove esi,eax */
static const uint8_t JAO_NEW[3]  = {0x31, 0xf6, 0x90}; /* xor esi,esi;nop */

/* All RDR2 PS4 title IDs listed in the eboot's region table. */
static const char *const WANT_TITLEIDS[] = {
    "CUSA03041",
    "CUSA08519",
    "CUSA08568",
    "CUSA15698",
};
#define N_WANT (sizeof(WANT_TITLEIDS) / sizeof(WANT_TITLEIDS[0]))

static int is_want(const char *tid) {
    unsigned i;
    for (i = 0; i < N_WANT; i++)
        if (!strcmp(tid, WANT_TITLEIDS[i]))
            return 1;
    return 0;
}

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

/* read exactly n bytes or fail */
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
    sa.sin_addr.s_addr = htonl(0x7f000001u); /* 127.0.0.1 */
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
    /* trailing data: text + NUL */
    if (sendn((const uint8_t *)msg, len)) {
        tlog("NOTIFY_DATA_FAIL");
        return -1;
    }
    rc = expect_success();
    snprintf(lb, sizeof(lb), "NOTIFY rc=%d msg=%.64s", rc, msg);
    tlog(lb);
    return rc;
}

/* foreground app: pid + titleid. pid==0 when no game is in front. */
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

/* local memmem in case the payload libc lacks it */
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

/* base = start of the lowest RX 'executable' segment (home of .text) */
static int eboot_base(uint32_t pid, uint64_t *base) {
    uint8_t b[4], hdr[8];
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
        if (sz < 0x1000000) /* eboot .text is tens of MB */
            continue;
        if (best == 0 || start < best)
            best = start;
    }
    if (!best)
        return -1;
    *base = best;
    return 0;
}

/* one-shot flow: fast-path 64-byte context check, MAPS fallback on mismatch.
 * Fast-path reads 64 B at fast_base+RVA-32; an exact JAO_CTX match makes the
 * target safe without downloading MAPS (spawn->write ~1 s). Poll every 0.5 s. */
#define AGGRESSIVE_CYCLES 360
#define POLL_FAST_USEC 500000u
#define POLL_SPARSE_SEC 15u
#define MAX_NOTIFIES_PER_PID 3u
#define AUTOPATCH_VERSION "oneshot-1.2"

int main(void) {
    uint32_t pid = 0;
    char titleid[16] = {0};
    uint64_t base = 0, target = 0;
    uint8_t ctx[64], cur[3];
    int have_target = 0;
    unsigned waited = 0;
    char lb[128];
    const unsigned LIMIT = 1200; /* 1200 x 0.5 s = 10 min */

    printf("autopatch60 v%s (one-shot): waiting for game...\n", AUTOPATCH_VERSION);
    tlog("BOOT oneshot");
    if (g_sock < 0 && connect_dbg()) {
        tlog("CONN_FAIL0");
        return 2;
    }
    tlog("CONN_OK");
    /* 1) wait for spawn */
    for (waited = 0; waited < LIMIT; waited++) {
        if (fg_app(&pid, titleid))
            break; /* dead connection: exit, nothing to patch */
        if (pid && is_want(titleid))
            break;
        usleep(POLL_FAST_USEC);
    }
    if (waited >= LIMIT || !pid || !is_want(titleid)) {
        tlog("TIMEOUT_NO_GAME");
        return 0; /* quiet exit: nothing was ever launched */
    }
    snprintf(lb, sizeof(lb), "SPAWN pid=%u tid=%.9s", pid, titleid);
    tlog(lb);
    /* 2) resolve target: CTX fast-path, MAPS fallback */
    target = IMG_BASE_DEFAULT + JAO_RVA;
    if (!proc_read(pid, target - JAO_CTX_OFF, ctx, 64) &&
        !memcmp(ctx, JAO_CTX, 64)) {
        have_target = 1;
    } else if (!eboot_base(pid, &base)) {
        target = base + JAO_RVA;
        snprintf(lb, sizeof(lb), "BASE 0x%llx pid=%u",
                 (unsigned long long)base, pid);
        tlog(lb);
        if (!proc_read(pid, target - JAO_CTX_OFF, ctx, 64) &&
            !memcmp(ctx, JAO_CTX, 64)) {
            have_target = 1;
        }
    }
    if (!have_target) {
        tlog("NO_TARGET");
        notify("RDR2 60fps: target not found, not applied");
        return 3;
    }
    /* 3) verify -> write -> re-verify -> notify -> exit */
    memcpy(cur, ctx + JAO_CTX_OFF, 3);
    if (!memcmp(cur, JAO_NEW, 3)) {
        tlog("ALREADY");
        notify("RDR2 60fps ON - made by KurohaXR");
        return 0;
    }
    if (memcmp(cur, JAO_ORIG, 3) != 0) {
        snprintf(lb, sizeof(lb), "ABORT_UNEXP %02x%02x%02x pid=%u",
                 cur[0], cur[1], cur[2], pid);
        tlog(lb);
        notify("RDR2 60fps: unexpected eboot, not applied");
        return 4;
    }
    tlog("WRITE_TRY");
    if (proc_write(pid, target, JAO_NEW, 3) ||
        proc_read(pid, target, cur, 3) ||
        memcmp(cur, JAO_NEW, 3) != 0) {
        tlog("WRITE_FAIL");
        notify("RDR2 60fps: write failed, not applied");
        return 5;
    }
    tlog("WRITE_OK");
    notify("RDR2 60fps ON - made by KurohaXR");
    printf("autopatch60: applied and verified, exiting.\n");
    return 0;
}
