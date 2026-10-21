/* Simulated annealing for the contextuality degree: minimise the number of violated lines over all
   +-1 assignments.  Usage: anneal INSTANCE SEED STEPS RESTARTS   (INSTANCE from dump_instance.py).
   Prints the best value of each restart; this is heuristic and gives upper bounds only. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned long long s = 88172645463325252ULL;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: anneal INSTANCE SEED STEPS RESTARTS\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    int P, L;
    if (!f || fscanf(f, "%d %d", &P, &L) != 2) return 1;
    int (*ln)[4] = malloc(sizeof(int[4]) * L), *deg = calloc(P, sizeof(int)), **inc = malloc(sizeof(int *) * P);
    int *x = malloc(sizeof(int) * P), *viol = malloc(sizeof(int) * L);
    for (int i = 0; i < L; i++) {
        if (fscanf(f, "%d %d %d %d", &ln[i][0], &ln[i][1], &ln[i][2], &ln[i][3]) != 4) return 1;
        for (int j = 0; j < 3; j++) deg[ln[i][j]]++;
    }
    for (int p = 0; p < P; p++) { inc[p] = malloc(sizeof(int) * deg[p]); deg[p] = 0; }
    for (int i = 0; i < L; i++)
        for (int j = 0; j < 3; j++) { int p = ln[i][j]; inc[p][deg[p]++] = i; }
    s += atoi(argv[2]);
    long steps = atol(argv[3]);
    for (int rest = 0; rest < atoi(argv[4]); rest++) {
        int cur = 0, best;
        for (int p = 0; p < P; p++) x[p] = rnd() & 1;
        for (int i = 0; i < L; i++) { viol[i] = x[ln[i][0]] ^ x[ln[i][1]] ^ x[ln[i][2]] ^ ln[i][3]; cur += viol[i]; }
        best = cur;
        for (long it = 0; it < steps; it++) {
            double T = 3.0 * pow(0.05 / 3.0, (double)it / steps);     /* geometric cooling from 3 to 0.05 */
            int p = rnd() % P, d = 0;
            for (int k = 0; k < deg[p]; k++) d += viol[inc[p][k]] ? -1 : 1;
            if (d <= 0 || (rnd() % 1000000) / 1e6 < exp(-d / T)) {
                x[p] ^= 1; cur += d;
                for (int k = 0; k < deg[p]; k++) viol[inc[p][k]] ^= 1;
                if (cur < best) best = cur;
            }
        }
        printf("restart %d: best %d\n", rest, best);
        fflush(stdout);
    }
    return 0;
}
