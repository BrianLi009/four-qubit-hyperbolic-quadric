/* Independent checker for deg Q-(7,2) >= 315, part 2: the exhaustive parts, on the data of check_setup.py.
   Notation: the outside values y are given by z (pair parities) and r (values on the representatives); k_a counts the
   12 complement lines at a in H violated when x_a = 0; f(y) = sum_a min(k_a, 12 - k_a); every assignment violates
   at least f(y) complement lines plus deg H >= 63 lines of H, so one with fewer than TARGET violations has
   f(y) <= TARGET - 1 - 63.

     check_cert setup.txt orbits.txt leaves.txt orbits
         the orbits of the listed representatives under the signed reflections and the complementation z -> ~z
         cover all 2^28 vectors z.
     check_cert setup.txt orbits.txt leaves.txt leaves
         every doily has degree 3 (so deg H >= 63), and for every representative z the r with r_K = 0 and
         f <= TARGET - 64 are exactly the leaves listed for z.
     check_cert setup.txt orbits.txt leaves.txt bounds k n cert.bin...
         for the leaves with index = k mod n: every completion x on H violates at least TARGET lines in total.
         A leaf with a record in the certificate is checked node by node: the fixings of its nodes cover all x,
         and for each node, with integer multipliers B (scale S = PC * 2^20) satisfying the constraints exactly,
         S * (sum of costs) + sum_D min_{x on D consistent with the fixings} [viol_D(x) S / LCV + sum_k B_{D,k} x_k]
         exceeds (TARGET - 1) S.  A leaf without a record is checked with the uniform split B = (c1 - c0) S / PC.
   All arithmetic is in 64-bit integers. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NP 28
#define NH 63
#define MAXD 1008
int ND, LCV, PC, TARGET, K[7], ngen, isK[NP];
int ce[NH][12][5], hl[315][4], dp[MAXD][15], lmask[MAXD][15], sgn[MAXD], perm[64][NP], add[64][NP];
uint32_t *reps; int nreps;
typedef struct { uint32_t z, r; int f; } leaf;
leaf *lv; int nleaves;
static int cmp(const void *a, const void *b) {
    const leaf *x = a, *y = b;
    if (x->z != y->z) return x->z < y->z ? -1 : 1;
    return x->r < y->r ? -1 : x->r > y->r;
}
static long find(uint32_t z, uint32_t r) {
    leaf key = {z, r, 0}; leaf *p = bsearch(&key, lv, nleaves, sizeof(leaf), cmp);
    return p ? p - lv : -1;
}
static void fail(const char *m) { printf("FAIL: %s\n", m); exit(1); }
static int mn(int a, int b) { return a < b ? a : b; }

static void read_input(char **argv) {
    FILE *f = fopen(argv[1], "r"); int np, nh;
    if (!f || fscanf(f, "%d %d %d %d %d %d", &np, &nh, &ND, &LCV, &PC, &TARGET) != 6 || np != NP || nh != NH || ND > MAXD) fail("setup");
    for (int a = 0; a < NH; a++) for (int e = 0; e < 12; e++) for (int t = 0; t < 5; t++) if (fscanf(f, "%d", &ce[a][e][t]) != 1) fail("setup");
    for (int i = 0; i < 315; i++) for (int t = 0; t < 4; t++) if (fscanf(f, "%d", &hl[i][t]) != 1) fail("setup");
    for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) if (fscanf(f, "%d", &dp[d][k]) != 1) fail("setup");
    for (int k = 0; k < 7; k++) { if (fscanf(f, "%d", &K[k]) != 1) fail("setup"); isK[K[k]] = 1; }
    if (fscanf(f, "%d", &ngen) != 1 || ngen > 64) fail("setup");
    for (int g = 0; g < ngen; g++) for (int k = 0; k < NP; k++) if (fscanf(f, "%d %d", &perm[g][k], &add[g][k]) != 2) fail("setup");
    fclose(f);
    /* local structure of each doily: the lines of H inside it */
    for (int d = 0; d < ND; d++) {
        int nl = 0; sgn[d] = 0; memset(lmask[d], 0, sizeof lmask[d]);
        for (int i = 0; i < 315; i++) {
            int loc[3], ok = 1;
            for (int t = 0; t < 3; t++) { loc[t] = -1; for (int k = 0; k < 15; k++) if (dp[d][k] == hl[i][t]) loc[t] = k; if (loc[t] < 0) ok = 0; }
            if (!ok) continue;
            for (int t = 0; t < 3; t++) lmask[d][loc[t]] |= 1 << nl;
            sgn[d] |= hl[i][3] << nl; nl++;
        }
        if (nl != 15) fail("a doily does not contain 15 lines");
    }
    f = fopen(argv[2], "r"); unsigned z; int a1, a2; long long sz; reps = malloc(4 * 1000); nreps = 0;
    while (fscanf(f, "%u %d %d %lld", &z, &a1, &a2, &sz) == 4) reps[nreps++] = z;
    fclose(f);
    f = fopen(argv[3], "r"); lv = malloc(sizeof(leaf) * 500000); nleaves = 0;
    unsigned r; int fl;
    while (fscanf(f, "%u %u %d%*[^\n]", &z, &r, &fl) == 3) { lv[nleaves].z = z; lv[nleaves].r = r; lv[nleaves].f = fl; nleaves++; }
    fclose(f);
    qsort(lv, nleaves, sizeof(leaf), cmp);
    for (int i = 1; i < nleaves; i++) if (!cmp(&lv[i - 1], &lv[i])) fail("duplicate leaf");
}

/* ---- orbits ---- */
static uint32_t apply(int g, uint32_t z) {
    uint32_t w = 0;
    if (g == ngen) return z ^ ((1u << NP) - 1);       /* complementation, by a functional with value 1 at v0 */
    for (int k = 0; k < NP; k++) w |= ((z >> k & 1) ^ add[g][k]) << perm[g][k];
    return w;
}
static void mode_orbits(void) {
    uint8_t *seen = calloc(1u << (NP - 3), 1); uint32_t *st = malloc(4u << NP); long long tot = 0;
    for (int i = 0; i < nreps; i++) {
        uint32_t z = reps[i]; if (seen[z >> 3] >> (z & 7) & 1) fail("two representatives in one orbit");
        long sp = 0; st[sp++] = z; seen[z >> 3] |= 1 << (z & 7); tot++;
        while (sp) {
            uint32_t u = st[--sp];
            for (int g = 0; g <= ngen; g++) {
                uint32_t w = apply(g, u);
                if (!(seen[w >> 3] >> (w & 7) & 1)) { seen[w >> 3] |= 1 << (w & 7); st[sp++] = w; tot++; }
            }
        }
    }
    printf("orbits: %d representatives cover %lld of %u vectors z\n", nreps, tot, 1u << NP);
    if (tot != (1ll << NP)) fail("orbits do not cover");
}

/* ---- doily degree and leaves ---- */
static int doily_min(int d) {
    int m = sgn[d], best = __builtin_popcount(m);
    for (int i = 1; i < 32768; i++) { int k = __builtin_ctz(i); m ^= lmask[d][k]; int v = __builtin_popcount(m); if (v < best) best = v; }
    return best;
}
static void mode_leaves(void) {
    for (int d = 0; d < ND; d++) if (doily_min(d) != 3) fail("doily degree");
    int hb = ND * 3; if (hb % LCV) fail("H bound"); hb /= LCV;
    int BEST = TARGET - 1 - hb;
    printf("every doily has degree 3, so deg H >= %d; leaves need f <= %d\n", hb, BEST);
    /* complement lines through each pair */
    static int ta[NP][64], te[NP][64], nt[NP];
    for (int a = 0; a < NH; a++) for (int e = 0; e < 12; e++) {
        int p1 = ce[a][e][0], p2 = ce[a][e][2];
        if (p1 == p2) fail("complement line with two points of one pair");
        ta[p1][nt[p1]] = a; te[p1][nt[p1]++] = e; ta[p2][nt[p2]] = a; te[p2][nt[p2]++] = e;
    }
    int freek[NP], nf = 0; for (int k = 0; k < NP; k++) if (!isK[k]) freek[nf++] = k;
    long long found = 0, listed = 0;
    for (int i = 0; i < nreps; i++) {
        uint32_t z = reps[i], r = 0; int vio[NH][12], kk[NH], f = 0;
        for (int a = 0; a < NH; a++) {
            kk[a] = 0;
            for (int e = 0; e < 12; e++) {
                int yb = (r >> ce[a][e][0] & 1) ^ (ce[a][e][1] ? z >> ce[a][e][0] & 1 : 0);
                int yc = (r >> ce[a][e][2] & 1) ^ (ce[a][e][3] ? z >> ce[a][e][2] & 1 : 0);
                vio[a][e] = yb ^ yc ^ ce[a][e][4]; kk[a] += vio[a][e];
            }
            f += mn(kk[a], 12 - kk[a]);
        }
        long nb = 0;
        for (uint32_t g = 0;; g++) {
            if (g) {
                int k = freek[__builtin_ctz(g)]; r ^= 1u << k;     /* flips y on both points of pair k */
                for (int t = 0; t < nt[k]; t++) {
                    int a = ta[k][t], e = te[k][t], old = mn(kk[a], 12 - kk[a]);
                    vio[a][e] ^= 1; kk[a] += vio[a][e] ? 1 : -1; f += mn(kk[a], 12 - kk[a]) - old;
                }
            }
            if (f <= BEST) {
                long j = find(z, r);
                if (j < 0) { printf("z %u r %u f %d\n", z, r, f); fail("a leaf is missing"); }
                if (lv[j].f != f) fail("f differs");
                nb++;
            }
            if (g == (1u << nf) - 1) break;
        }
        /* count all leaves with this z (the array is sorted by z) */
        long cnt = 0; { leaf key = {z, 0, 0}; long lo = 0, hi = nleaves; while (lo < hi) { long m = (lo + hi) / 2; if (cmp(&lv[m], &key) < 0) lo = m + 1; else hi = m; } while (lo < nleaves && lv[lo].z == z) { cnt++; lo++; } }
        if (cnt != nb) fail("extra leaves listed");
        found += nb; listed += cnt;
    }
    for (int i = 0; i < nleaves; i++) for (int k = 0; k < 7; k++) if (lv[i].r >> K[k] & 1) fail("leaf not gauge-fixed");
    /* every listed leaf has a representative z */
    if (listed != nleaves) fail("leaf with a z that is not a representative");
    printf("leaves: %d representatives, %lld leaves found, all listed, nothing else listed\n", nreps, found);
}

/* ---- bounds ---- */
long long S, W;
static void costs(const leaf *l, int *c0, int *c1) {
    for (int a = 0; a < NH; a++) {
        int k0 = 0;
        for (int e = 0; e < 12; e++) {
            int yb = (l->r >> ce[a][e][0] & 1) ^ (ce[a][e][1] ? l->z >> ce[a][e][0] & 1 : 0);
            int yc = (l->r >> ce[a][e][2] & 1) ^ (ce[a][e][3] ? l->z >> ce[a][e][2] & 1 : 0);
            k0 += yb ^ yc ^ ce[a][e][4];
        }
        c0[a] = k0; c1[a] = 12 - k0;
    }
}
/* bound * S for one node; fixed[a] = -1 (free) or the value */
static long long node_bound(const int *c0, const int *c1, const int *fixed, long long (*Bm)[15]) {
    long long lb = 0;
    for (int a = 0; a < NH; a++) lb += (long long)(fixed[a] == 1 ? c1[a] : c0[a]) * S;
    static long long sum[NH]; memset(sum, 0, sizeof sum);
    for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) sum[dp[d][k]] += Bm[d][k];
    for (int a = 0; a < NH; a++) if (fixed[a] < 0 && sum[a] != (long long)(c1[a] - c0[a]) * S) fail("multipliers violate a constraint");
    for (int d = 0; d < ND; d++) {
        int fm = 0, fv = 0; long long b[15];
        for (int k = 0; k < 15; k++) {
            int a = dp[d][k];
            if (fixed[a] >= 0) { fm |= 1 << k; fv |= fixed[a] << k; b[k] = 0; } else b[k] = Bm[d][k];
        }
        int m = sgn[d], x = 0; long long acc = 0, best = (fv == 0) ? __builtin_popcount(m) * W : INT64_MAX;
        for (int i = 1; i < 32768; i++) {
            int k = __builtin_ctz(i); x ^= 1 << k; m ^= lmask[d][k];
            acc += (x >> k & 1) ? b[k] : -b[k];
            if ((x & fm) != fv) continue;
            long long v = __builtin_popcount(m) * W + acc;
            if (v < best) best = v;
        }
        lb += best;
    }
    return lb;
}
static void mode_bounds(int kk, int nn, int nc, char **cf) {
    S = (long long)PC << 20; if (S % LCV) fail("scale"); W = S / LCV;
    long long need = (long long)(TARGET - 1) * S;
    char *done = calloc(nleaves, 1); long nrec = 0, nnodes = 0;
    static long long Bm[MAXD][15]; int c0[NH], c1[NH], fixed[NH];
    int32_t *raw = malloc(4 * MAXD * 15);
    for (int c = 0; c < nc; c++) {
        FILE *f = fopen(cf[c], "rb"); if (!f) fail("certificate file");
        int32_t h[3];
        while (fread(h, 4, 3, f) == 3) {
            long j = find((uint32_t)h[0], (uint32_t)h[1]); if (j < 0) fail("record for a pair that is not a leaf");
            int mine = j % nn == kk; if (mine && done[j]) fail("two records for one leaf");
            if (mine) costs(&lv[j], c0, c1);
            int nfx[64], fa[64][64], fvv[64][64], nnode = h[2]; if (nnode < 1 || nnode > 64) fail("node count");
            for (int t = 0; t < nnode; t++) {
                int32_t nf; if (fread(&nf, 4, 1, f) != 1 || nf < 0 || nf > 63) fail("read");
                nfx[t] = nf;
                for (int i = 0; i < nf; i++) { int32_t p[2]; if (fread(p, 4, 2, f) != 2 || p[0] < 0 || p[0] >= NH || (p[1] & ~1)) fail("read"); fa[t][i] = p[0]; fvv[t][i] = p[1]; }
                if (fread(raw, 4, ND * 15, f) != (size_t)ND * 15) fail("read");
                if (!mine) continue;
                for (int a = 0; a < NH; a++) fixed[a] = -1;
                for (int i = 0; i < nf; i++) { if (fixed[fa[t][i]] >= 0) fail("point fixed twice"); fixed[fa[t][i]] = fvv[t][i]; }
                for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) Bm[d][k] = raw[d * 15 + k];
                if (node_bound(c0, c1, fixed, Bm) <= need) { printf("leaf z %u r %u node %d\n", lv[j].z, lv[j].r, t); fail("bound too small"); }
                nnodes++;
            }
            if (!mine) continue;
            /* the fixings of the nodes cover every x: enumerate the values of the points they involve */
            int pts[64], np = 0;
            for (int t = 0; t < nnode; t++) for (int i = 0; i < nfx[t]; i++) { int a = fa[t][i], s = 0; for (int q = 0; q < np; q++) s |= pts[q] == a; if (!s) pts[np++] = a; }
            if (np > 20) fail("too many branching points");
            for (uint32_t m = 0; m < (1u << np); m++) {
                int cov = 0;
                for (int t = 0; t < nnode && !cov; t++) {
                    int ok = 1;
                    for (int i = 0; i < nfx[t]; i++) { int q = 0; while (pts[q] != fa[t][i]) q++; if ((int)(m >> q & 1) != fvv[t][i]) ok = 0; }
                    cov = ok;
                }
                if (!cov) fail("the nodes do not cover all completions");
            }
            done[j] = 1; nrec++;
        }
        fclose(f);
    }
    long nuni = 0;
    for (long j = kk; j < nleaves; j += nn) {
        if (done[j]) continue;
        costs(&lv[j], c0, c1);
        for (int a = 0; a < NH; a++) fixed[a] = -1;
        for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) { int a = dp[d][k]; Bm[d][k] = (long long)(c1[a] - c0[a]) * (S / PC); }
        if (node_bound(c0, c1, fixed, Bm) <= need) { printf("leaf z %u r %u, uniform split\n", lv[j].z, lv[j].r); fail("bound too small"); }
        nuni++;
    }
    printf("bounds part %d of %d: %ld leaves by the uniform split, %ld by certificate records (%ld nodes), all > %d\n", kk, nn, nuni, nrec, nnodes, TARGET - 1);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: see the header\n"); return 2; }
    read_input(argv);
    if (!strcmp(argv[4], "orbits")) mode_orbits();
    else if (!strcmp(argv[4], "leaves")) mode_leaves();
    else if (!strcmp(argv[4], "bounds") && argc >= 7) mode_bounds(atoi(argv[5]), atoi(argv[6]), argc - 7, argv + 7);
    else return 2;
    return 0;
}
