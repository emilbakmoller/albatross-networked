#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/vector.h>

using namespace std;
using namespace NTL;

typedef struct pl_t pl_t;

void prng_init(const unsigned int seed);

/* allocate the memory for the publice ledger */
pl_t *pl_alloc(const int n);

/* liberate the memory of the public ledger */
void pl_free(pl_t *pl);

/* print the public ledger */
void pl_print(pl_t *pl);

/* compute a generator of the multiplicative group Zq */
void generator(ZZ_p& g, const ZZ& q);

/* setup return the public ledger
and create the public keys and secret keys for n participants */
pl_t *setup(Vec<ZZ_p>& sk, const int n, const ZZ& q, const ZZ& p, const ZZ_p& h);

/* t threshold, l number of secrets
add the encrypted shares in he public ledger */
void distribution(const int l, const int t, pl_t *pl);

/* compute the list of lambda to compute the secrets */
void lambda(Mat<ZZ_p>& lamb, int t, pl_t *pl);

/* reconstruct the secret vector */
void reconstruction(Vec<ZZ>& S, const int r, pl_t *pl);
