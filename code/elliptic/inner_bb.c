/* Second stage of deg Q-(7,2) >= 315.  For each leaf (z, r) of zcount.c, the values y on the 56 points outside
   v0^perp are fixed, and what remains is the parabolic section H (63 points, 315 lines) with unary costs:
       min_x  sum_a c_{x_a}(a) + #violated lines of H,   c_0(a) = k_a, c_1(a) = 12 - k_a,
   where k_a counts the complement lines at a violated when x_a = 0.  We show that this is >= TARGET.
   Lower bound: Lagrangian decomposition over a doily family of H covering every line LCV and every point PC times,
       LB(beta) = sum_a c_0(a) + sum_D min_{x in F_2^15} [ viol_D(x) / LCV + sum_k beta_{D,k} x_k ],
   valid whenever sum over the doilies D at a of beta_{D,a} = c_1(a) - c_0(a); each doily minimum is taken over all
   2^15 local assignments (Gray code).  The multipliers start from the uniform split and follow subgradient steps.
   Upper bound: the majority vote of the doily minimisers, evaluated exactly.  If the bound stays below TARGET,
   branch on the point whose doily votes are most split (a cost of 1000 forbids a value).
   Usage: inner_bb zdata.txt hdata.txt leaves.txt TARGET MAXIT [cert.bin]   (compile with -DND=1008 for the quadratic family)
   With cert.bin, a leaf counts as settled only if its bound exceeds TARGET - 1 by 2e-4, and for every leaf not settled
   by the uniform split the multipliers of each node of its branching tree are written, scaled by S = PC * 2^20 and
   rounded so that the constraints hold exactly in integers (fixed points get 0), for certificate/check_cert.c:
       int32 z, r, nnodes; per node: int32 nfix, nfix pairs (point, value), ND * 15 int32 multipliers.
   Output per leaf: z r f status rootLB UB nodes rootiterations, status P = every completion violates >= TARGET lines,
   C = a completion with fewer was found, U = undecided. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define NPAIR 28
#define NH 63
#define NL 315
#ifndef ND
#define ND 336
#endif
#define PC (ND * 15 / 63)
#define LCV (ND * 15 / 315)
int eb[NH][12], tb[NH][12], ec[NH][12], tc[NH][12], es[NH][12];
int hl[NL][4], dp[ND][15], dl[ND][15], vig[ND][32768], ptoD[NH][PC], ptoK[NH][PC], npt[NH];
double beta[ND][15];
int TARGET, MAXIT, lastits, rootits; long nodes;
int xs[ND];
FILE *certf; double MARGIN = 1e-6;
#define SCALE ((double)PC * 1048576.0)
int nfix, fixa[64], fixv[64], nbuf; int32_t *buf; size_t buflen, bufcap;
static void put(int32_t v) { if (buflen == bufcap) { bufcap = bufcap ? 2 * bufcap : 1 << 20; buf = realloc(buf, bufcap * 4); } buf[buflen++] = v; }
/* record the current multipliers for a settled node, rounded so that sum_D B[D][a] = (c1 - c0) S at free points */
static void record(const int *c0, const int *c1) {
    static long long B[ND][15]; int fixed[NH] = {0};
    for (int i = 0; i < nfix; i++) fixed[fixa[i]] = 1;
    for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) B[d][k] = fixed[dp[d][k]] ? 0 : llround(beta[d][k] * SCALE);
    for (int a = 0; a < NH; a++) if (!fixed[a]) {
        long long s = 0; for (int t = 0; t < PC; t++) s += B[ptoD[a][t]][ptoK[a][t]];
        B[ptoD[a][0]][ptoK[a][0]] += (long long)(c1[a] - c0[a]) * (long long)SCALE - s;
    }
    put(nfix); for (int i = 0; i < nfix; i++) { put(fixa[i]); put(fixv[i]); }
    for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) {
        if (B[d][k] > INT32_MAX || B[d][k] < INT32_MIN) { fprintf(stderr, "multiplier overflow\n"); exit(5); }
        put((int32_t)B[d][k]);
    }
    nbuf++;
}
/* Lagrangian bound for costs c0, c1 (branching = huge cost on one side); returns status, fills best/UB */
char lag(const int *c0, const int *c1, int maxit, double *pbest, int *pUB) {
    static double g[ND][15]; int xmaj[NH]; double cst = 0;
    for (int a = 0; a < NH; a++) cst += c0[a];
    for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) beta[d][k] = (c1[dp[d][k]] - c0[dp[d][k]]) / (double)PC;
    double best = -1e9; int UB = *pUB; char status = 'U';
    int it;
    for (it = 0; it < maxit; it++) {
        double lb = cst;
        for (int d = 0; d < ND; d++) {
            double acc = 0, bv = vig[d][0] / (double)LCV; int x = 0, bx = 0;
            double *bt = beta[d]; int *vg = vig[d];
            for (int i = 1; i < 32768; i++) {
                int k = __builtin_ctz(i); x ^= 1 << k;
                acc += (x >> k & 1) ? bt[k] : -bt[k];
                double v = vg[i] * (1.0 / LCV) + acc;
                if (v < bv) { bv = v; bx = x; }
            }
            lb += bv; xs[d] = bx;
        }
        if (lb > best) best = lb;
        for (int a = 0; a < NH; a++) {
            int s = 0; for (int t = 0; t < PC; t++) s += xs[ptoD[a][t]] >> ptoK[a][t] & 1;
            xmaj[a] = s * 2 > PC ? 1 : (s * 2 < PC ? 0 : (c1[a] < c0[a]));
        }
        int ub = 0;
        for (int a = 0; a < NH; a++) ub += xmaj[a] ? c1[a] : c0[a];
        for (int i = 0; i < NL; i++) ub += xmaj[hl[i][0]] ^ xmaj[hl[i][1]] ^ xmaj[hl[i][2]] ^ hl[i][3];
        if (ub < UB) UB = ub;
        if (UB < TARGET) { status = 'C'; break; }
        if (best > TARGET - 1 + MARGIN) { status = 'P'; break; }
        double g2 = 0;
        for (int a = 0; a < NH; a++) {
            double m = 0; for (int t = 0; t < PC; t++) m += xs[ptoD[a][t]] >> ptoK[a][t] & 1;
            m /= PC;
            for (int t = 0; t < PC; t++) { double gg = (xs[ptoD[a][t]] >> ptoK[a][t] & 1) - m; g[ptoD[a][t]][ptoK[a][t]] = gg; g2 += gg * gg; }
        }
        if (g2 < 1e-12) break;
        double tgt = (UB < TARGET + 3 ? UB : TARGET + 3);
        double step = (tgt - lb) / g2; if (step < 1e-4) step = 1e-4;
        for (int d = 0; d < ND; d++) for (int k = 0; k < 15; k++) beta[d][k] += step * g[d][k];
    }
    *pbest = best; *pUB = UB; lastits = it; return status;
}
/* branch and bound: returns 'P' if every completion costs >= TARGET, 'C' if a completion < TARGET exists */
char bb(int *c0, int *c1, int depth, int *pUB, double *rootlb) {
    nodes++;
    double best; char st = lag(c0, c1, MAXIT, &best, pUB);
    if (depth == 0) { *rootlb = best; rootits = lastits; }
    if (st == 'P' && certf) record(c0, c1);
    if (st != 'U') return st;
    if (depth > 40) return 'U';
    /* branch on the free point whose doily votes are most split */
    int ba = -1; double bd = 2;
    for (int a = 0; a < NH; a++) {
        if (c0[a] >= 1000 || c1[a] >= 1000) continue;
        int s = 0; for (int t = 0; t < PC; t++) s += xs[ptoD[a][t]] >> ptoK[a][t] & 1;
        double dd = fabs(s / (double)PC - 0.5);
        if (dd < bd) { bd = dd; ba = a; }
    }
    if (ba < 0) return 'U';
    int s0 = c0[ba], s1 = c1[ba]; char r;
    fixa[nfix] = ba; fixv[nfix++] = 0;
    c1[ba] = 1000; r = bb(c0, c1, depth + 1, pUB, rootlb); c1[ba] = s1; nfix--;
    if (r != 'P') return r;
    fixa[nfix] = ba; fixv[nfix++] = 1;
    c0[ba] = 1000; r = bb(c0, c1, depth + 1, pUB, rootlb); c0[ba] = s0; nfix--;
    return r;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int np, nh, tmp;
    if (fscanf(f, "%d %d", &np, &nh) != 2 || np != NPAIR || nh != NH) return 1;
    for (int a = 0; a < NH; a++) for (int e = 0; e < 12; e++)
        if (fscanf(f, "%d %d %d %d %d", &eb[a][e], &tb[a][e], &ec[a][e], &tc[a][e], &es[a][e]) != 5) return 1;
    fclose(f);
    f = fopen(argv[2], "r"); int n1, n2, n3;
    if (fscanf(f, "%d %d %d", &n1, &n2, &n3) != 3 || n1 != NH || n2 != NL || n3 != ND) return 2;
    for (int i = 0; i < NL; i++) for (int j = 0; j < 4; j++) tmp = fscanf(f, "%d", &hl[i][j]);
    for (int d = 0; d < ND; d++) { for (int k = 0; k < 15; k++) tmp = fscanf(f, "%d", &dp[d][k]); for (int k = 0; k < 15; k++) tmp = fscanf(f, "%d", &dl[d][k]); }
    fclose(f);
    for (int d = 0; d < ND; d++) {
        for (int k = 0; k < 15; k++) { int a = dp[d][k]; ptoD[a][npt[a]] = d; ptoK[a][npt[a]] = k; npt[a]++; }
        /* local incidence */
        int lmask[15] = {0};    /* local point k -> mask of local lines */
        int sgn = 0;
        for (int j = 0; j < 15; j++) {
            int li = dl[d][j]; sgn |= hl[li][3] << j;
            for (int t = 0; t < 3; t++) for (int k = 0; k < 15; k++) if (dp[d][k] == hl[li][t]) lmask[k] |= 1 << j;
        }
        int x = 0, m = sgn;
        for (int i = 0; i < 32768; i++) {
            if (i) { int k = __builtin_ctz(i); x ^= 1 << k; m ^= lmask[k]; }
            vig[d][i] = __builtin_popcount(m);
        }
    }
    for (int a = 0; a < NH; a++) if (npt[a] != PC) { fprintf(stderr, "point cover %d\n", npt[a]); return 3; }
    FILE *lf = fopen(argv[3], "r"); TARGET = atoi(argv[4]); MAXIT = atoi(argv[5]);
    if (argc > 6) { certf = fopen(argv[6], "wb"); MARGIN = 2e-4; }
    unsigned z, rm; int fl;
    int c0[NH], c1[NH];
    while (fscanf(lf, "%u %u %d%*[^\n]", &z, &rm, &fl) == 3) {
        int y[2 * NPAIR];
        for (int k = 0; k < NPAIR; k++) { y[k] = rm >> k & 1; y[k + NPAIR] = (rm >> k & 1) ^ (z >> k & 1); }
        int fsum = 0;
        for (int a = 0; a < NH; a++) {
            int k0 = 0;
            for (int e = 0; e < 12; e++) k0 += y[eb[a][e] + NPAIR * tb[a][e]] ^ y[ec[a][e] + NPAIR * tc[a][e]] ^ es[a][e];
            c0[a] = k0; c1[a] = 12 - k0; fsum += k0 < 12 - k0 ? k0 : 12 - k0;
        }
        if (fsum != fl) { fprintf(stderr, "f mismatch\n"); return 4; }
        int UB = 1 << 30; double rootlb; nodes = 0;
        nfix = 0; nbuf = 0; buflen = 0;
        char st = bb(c0, c1, 0, &UB, &rootlb);
        if (certf && st == 'P' && !(nodes == 1 && rootits == 0)) {
            int32_t h[3] = {(int32_t)z, (int32_t)rm, nbuf};
            fwrite(h, 4, 3, certf); fwrite(buf, 4, buflen, certf); fflush(certf);
        }
        printf("%u %u %d %c %.4f %d %ld %d\n", z, rm, fl, st, rootlb, UB, nodes, rootits); fflush(stdout);
    }
    return 0;
}
