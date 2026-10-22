/* First stage of deg Q-(7,2) >= 315: list the leaves.  Same data, orbits and branch and bound as zorb.c, but
   instead of minimising f(y) = sum_a min(k_a, 12 - k_a) over the parabolic complement, list every gauge-fixed r with
   f <= BEST for each orbit representative z with min f <= BEST.  Every assignment of Q-(7,2) is equivalent, under the
   signed symmetries fixing v0 and the gauge, to one whose outside values are such a pair (z, r) or have f > BEST.
   Usage: zcount zdata.txt BEST orbits.txt [leaves.txt]   (orbits.txt as written by zorb: z P G size) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NP 28
#define NHM 63
int np, nh, eb[NHM][12], tb[NHM][12], ec[NHM][12], tc[NHM][12], es[NHM][12], fixr[7], ngen;
int gimg[16][56], gcor[16][56];
int zperm[17][NP], zadd[17][NP];          /* affine action on z: z'[zperm[k]] = z[k] ^ zadd[k] */
/* per-orbit structure */
int qa[NHM], pa_[NHM];
int dpb[NHM][6], dpc[NHM][6], dh[NHM][6];
int nd_at[NP], da[NP][64], dother[NP][64], dhh[NP][64];   /* doubled edges completed at rep position */
int order[NP], posof[NP], r[NP], oddc[NHM], evc[NHM], targetG;
long long bbnodes;
static inline int mn(int a, int b) { return a < b ? a : b; }
static inline int ybit(const int *rr, uint32_t z, int pair, int t) { return rr[pair] ^ (t ? (z >> pair) & 1 : 0); }
int f_direct(const int *rr, uint32_t z) {
    int tot = 0;
    for (int a = 0; a < nh; a++) {
        int k = 0;
        for (int e = 0; e < 12; e++) k += ybit(rr, z, eb[a][e], tb[a][e]) ^ ybit(rr, z, ec[a][e], tc[a][e]) ^ es[a][e];
        tot += mn(k, 12 - k);
    }
    return tot;
}
/* split structure for z: returns P(z); fills doubled edges */
int structure(uint32_t z) {
    int P = 0;
    for (int a = 0; a < nh; a++) {
        int used[12] = {0}; qa[a] = 0; pa_[a] = 0;
        for (int e = 0; e < 12; e++) {
            if (used[e]) continue;
            int f = -1;
            for (int g = e + 1; g < 12; g++)
                if (!used[g] && ((eb[a][g] == eb[a][e] && ec[a][g] == ec[a][e]) || (eb[a][g] == ec[a][e] && ec[a][g] == eb[a][e]))) { f = g; break; }
            if (f < 0) { fprintf(stderr, "unpaired edge\n"); exit(3); }
            used[e] = used[f] = 1;
            int h1 = es[a][e] ^ (tb[a][e] ? (z >> eb[a][e]) & 1 : 0) ^ (tc[a][e] ? (z >> ec[a][e]) & 1 : 0);
            int h2 = es[a][f] ^ (tb[a][f] ? (z >> eb[a][f]) & 1 : 0) ^ (tc[a][f] ? (z >> ec[a][f]) & 1 : 0);
            if (h1 != h2) pa_[a]++;
            else { dpb[a][qa[a]] = eb[a][e]; dpc[a][qa[a]] = ec[a][e]; dh[a][qa[a]] = h1; qa[a]++; }
        }
        P += pa_[a];
    }
    return P;
}
void prepare_bb(void) {
    memset(nd_at, 0, sizeof nd_at);
    for (int a = 0; a < nh; a++)
        for (int d = 0; d < qa[a]; d++) {
            int u = dpb[a][d], w = dpc[a][d];
            int hi = posof[u] > posof[w] ? u : w, lo = hi == u ? w : u;
            int p = posof[hi];
            da[p][nd_at[p]] = a; dother[p][nd_at[p]] = lo; dhh[p][nd_at[p]] = dh[a][d]; nd_at[p]++;
        }
}
FILE *leafdump; unsigned curz; int curP; int bestG; long long leafcnt, leafhist[128];
void bb(int i, int lb) {
    bbnodes++;
    if (i == np) { if (lb < bestG) bestG = lb; leafcnt++; if (lb < 128) leafhist[lb]++; if (leafdump) { unsigned m = 0; for (int k = 0; k < np; k++) m |= (unsigned)r[k] << k; fprintf(leafdump, "%u %u %d\n", curz, m, curP + 2 * lb); } return; }
    int pr = order[i];
    for (int v = 0; v < 2; v++) {
        int fixed = 0; for (int k = 0; k < 7; k++) if (fixr[k] == pr) fixed = 1;
        if (fixed && v) break;
        r[pr] = v;
        int nl = lb;
        for (int k = 0; k < nd_at[i]; k++) {
            int a = da[i][k]; int before = mn(oddc[a], evc[a]);
            if (v ^ r[dother[i][k]] ^ dhh[i][k]) oddc[a]++; else evc[a]++;
            nl += mn(oddc[a], evc[a]) - before;
        }
        if (nl <= targetG) bb(i + 1, nl);
        for (int k = 0; k < nd_at[i]; k++) {
            int a = da[i][k];
            if (v ^ r[dother[i][k]] ^ dhh[i][k]) oddc[a]--; else evc[a]--;
        }
    }
}
uint32_t apply(int g, uint32_t z) {
    uint32_t o = 0;
    for (int k = 0; k < np; k++) if (((z >> k) & 1) ^ zadd[g][k]) o |= 1u << zperm[g][k];
    return o;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int BEST = atoi(argv[2]); 
    if (fscanf(f, "%d %d", &np, &nh) != 2) return 1;
    for (int a = 0; a < nh; a++) for (int e = 0; e < 12; e++)
        if (fscanf(f, "%d %d %d %d %d", &eb[a][e], &tb[a][e], &ec[a][e], &tc[a][e], &es[a][e]) != 5) return 1;
    for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &fixr[k]) != 1) return 1;
    if (fscanf(f, "%d", &ngen) != 1) return 1;
    for (int g = 0; g < ngen; g++) for (int i = 0; i < 2 * np; i++) if (fscanf(f, "%d %d", &gimg[g][i], &gcor[g][i]) != 2) return 1;
    /* z action of each generator; check that pairs map to pairs */
    for (int g = 0; g < ngen; g++)
        for (int k = 0; k < np; k++) {
            int j1 = gimg[g][k], j2 = gimg[g][k + np];
            if (j1 % np != j2 % np || j1 == j2) { fprintf(stderr, "pair not preserved\n"); return 3; }
            zperm[g][k] = j1 % np; zadd[g][k] = gcor[g][k] ^ gcor[g][k + np];
        }
    for (int k = 0; k < np; k++) { zperm[ngen][k] = k; zadd[ngen][k] = 1; }   /* gauge: global flip */
    int nz = ngen + 1;
    /* self-checks on random points */
    srand(7);
    for (int t = 0; t < 2000; t++) {
        int rr[NP]; uint32_t z = 0;
        for (int k = 0; k < np; k++) { rr[k] = rand() & 1; if (rand() & 1) z |= 1u << k; }
        int fd = f_direct(rr, z);
        int P = structure(z), s = 0;
        for (int a = 0; a < nh; a++) { int j = 0; for (int d = 0; d < qa[a]; d++) j += rr[dpb[a][d]] ^ rr[dpc[a][d]] ^ dh[a][d]; s += mn(j, qa[a] - j); }
        if (fd != P + 2 * s) { fprintf(stderr, "pair formula mismatch %d vs %d\n", fd, P + 2 * s); return 4; }
        for (int g = 0; g < ngen; g++) {   /* invariance: y'_{img(i)} = y_i ^ cor_i */
            int y[56], y2[56], r2[NP]; uint32_t z2 = 0;
            for (int i = 0; i < 2 * np; i++) y[i] = ybit(rr, z, i % np, i >= np);
            for (int i = 0; i < 2 * np; i++) y2[gimg[g][i]] = y[i] ^ gcor[g][i];
            for (int k = 0; k < np; k++) { r2[k] = y2[k]; if (y2[k] ^ y2[k + np]) z2 |= 1u << k; }
            if (f_direct(r2, z2) != fd) { fprintf(stderr, "invariance fails gen %d\n", g); return 5; }
            if (z2 != apply(g, z)) { fprintf(stderr, "z action mismatch\n"); return 6; }
        }
    }
    fprintf(stderr, "self-checks passed\n");
    /* rep order: gauge-fixed reps first, then greedily by completed doubled edges (static, all edges) */
    int used[NP] = {0}, n = 0;
    for (int k = 0; k < 7; k++) { order[n++] = fixr[k]; used[fixr[k]] = 1; }
    while (n < np) {
        int bestk = -1, bs = -1;
        for (int k = 0; k < np; k++) if (!used[k]) {
            int s = 0;
            for (int a = 0; a < nh; a++) for (int e = 0; e < 12; e++)
                if ((eb[a][e] == k && used[ec[a][e]]) || (ec[a][e] == k && used[eb[a][e]])) s++;
            if (s > bs) { bs = s; bestk = k; }
        }
        order[n++] = bestk; used[bestk] = 1;
    }
    for (int i = 0; i < np; i++) posof[order[i]] = i;
    /* argv[3]: orbits file (z P G size); count r-leaves with f <= BEST for each listed orbit */
    leafdump = argc > 4 ? fopen(argv[4], "w") : NULL;
    FILE *of = fopen(argv[3], "r"); unsigned z; int P0, G0; long long osz; long long tot = 0, totw = 0;
    long long fh[400] = {0};
    while (fscanf(of, "%u %d %d %lld", &z, &P0, &G0, &osz) == 4) {
        if (P0 + 2 * G0 > BEST) continue;
        int P = structure(z); curz = z; curP = P;
        prepare_bb();
        memset(oddc, 0, sizeof oddc); memset(evc, 0, sizeof evc); memset(leafhist, 0, sizeof leafhist);
        bestG = 1 << 20; targetG = (BEST - P) / 2; leafcnt = 0;
        bb(0, 0);
        printf("z %u P %d minf %d size %lld leaves %lld\n", z, P, P + 2 * bestG, osz, leafcnt); fflush(stdout);
        for (int g = 0; g < 128; g++) if (P + 2 * g < 400) fh[P + 2 * g] += leafhist[g];
        tot += leafcnt; totw += leafcnt * osz;
    }
    printf("TOTAL leaves (orbit reps) %lld, weighted by orbit size %lld\n", tot, totw);
    for (int f = 0; f < 400; f++) if (fh[f]) printf("f %d count %lld\n", f, fh[f]);
    return 0;
}
