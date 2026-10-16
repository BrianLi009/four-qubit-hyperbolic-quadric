/* Exhaustive search over the 2^28 alternating bilinear forms beta on F_2^8 (remark "optimal assignments are not quadratic" in the paper).
   An assignment x = q (q a quadratic form with polar form beta) violates the line {u, v, u+v} iff
   beta(u, v) != s(line). Reads lines.txt written by prepare.py: for each line, its 28 coordinates
   beta_ij(u, v) = u_i v_j + u_j v_i (i < j) and its sign. Enumerates beta in Gray-code order. */
#include <stdio.h>
#include <stdint.h>
#define W 25                       /* 25 * 64 >= 1575 */
int main(void) {
    int n, m;
    FILE *f = fopen("lines.txt", "r");
    if (!f || fscanf(f, "%d %d", &n, &m) != 2 || n > 64 * W || m > 63) return 2;
    static uint64_t col[64][W], sig[W], cur[W];
    for (int l = 0; l < n; l++) {
        for (int k = 0; k < m; k++) { int b; if (fscanf(f, "%d", &b) != 1) return 2; if (b) col[k][l / 64] |= 1ULL << (l % 64); }
        int s; if (fscanf(f, "%d", &s) != 1) return 2; if (s) sig[l / 64] |= 1ULL << (l % 64);
    }
    for (int w = 0; w < W; w++) cur[w] = sig[w];
    int best = 0; for (int w = 0; w < W; w++) best += __builtin_popcountll(sig[w]);
    long count = 1;
    for (uint64_t g = 1; g < (1ULL << m); g++) {
        int k = __builtin_ctzll(g), d = 0;
        for (int w = 0; w < W; w++) { cur[w] ^= col[k][w]; d += __builtin_popcountll(cur[w]); }
        if (d < best) { best = d; count = 0; }
        if (d == best) count++;
    }
    printf("least number of violated lines over all quadratic assignments: %d (attained by %ld forms beta)\n", best, count);
    return 0;
}
