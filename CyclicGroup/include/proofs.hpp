#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/vector.h>
#include <NTL/ZZ_pX.h>

using namespace std;
using namespace NTL;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// LDEI ////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class LDEI {
  public:
    Vec<ZZ_p> a;
    ZZ_p e;
    ZZ_pX z;
    LDEI();
    LDEI(const Vec<ZZ_p>& a, const ZZ_p &e, const ZZ_pX &z);
    ~LDEI() {}
    void print();
    void prove(const ZZ& q, const Vec<ZZ_p>& g, const Vec<ZZ_p>& alpha, const long k, const Vec<ZZ_p>& x, const ZZ_pX& P);
    bool verify(const ZZ& q, const Vec<ZZ_p>& g, const Vec<ZZ_p>& alpha, const long k, const Vec<ZZ_p>& x);
};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// DLEQ ////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class DLEQ {
  public:
    Vec<ZZ_p> a;
    ZZ_p e;
    ZZ z;
    DLEQ();
    DLEQ(const Vec<ZZ_p>& a, const ZZ_p &e, const ZZ &z);
    ~DLEQ() {}
    void print();
    void prove(const ZZ& q, const Vec<ZZ_p>& g, const Vec<ZZ_p>& x, ZZ_p& alpha);
    bool verify(const ZZ& q, const Vec<ZZ_p>& g, const Vec<ZZ_p>& x);
};

////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// local LDEI ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool localldei(const ZZ& q, const ZZ& p, const Vec<ZZ_p>& alpha, const long k, const Vec<ZZ_p>& x, const long m);
