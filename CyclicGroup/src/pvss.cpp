/* implementation of pvss protocol */
#include <iostream>
#include <cstdlib>
#include <ctime>
#include <unistd.h>
#include <utility>
#include <vector>
#include <sstream>
#include <thread>

#include <NTL/ZZ_pX.h>
#include <sqlite3.h>

#include "pvss.hpp"
#include "proofs.hpp"
#include "func.hpp"
#include "hash.hpp"

// witness of distribution and reconstruction
bool dist = false;
bool rec = false;

////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// public ledger /////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct pl_t {
  int n; // number of participants
  int t; // threshold
  int l; // number of secrets
  int r; // number of participants who want to reconstruct the secrets
  ZZ q; // order of the group G_q
  ZZ p; // p = 2q+1
  ZZ_p h; // generator of G_q
  Vec<ZZ_p> pk; // publi keys
  Vec<ZZ_p> sighat; // encrypted shares  Map<sender_pk, Vec<ZZ_p>>
  LDEI ld; // proof LDEI
  int *reco_parties; // reconstructing party's identifiants
  Vec<ZZ_p> sigtilde; // decrypted shares and their index
  vector<DLEQ> dl; // proof DLEQ
  Vec<ZZ_p> S; // secrets reconstructed
};

pl_t *pl_alloc(const int n) {
  pl_t *pl;
  pl = new (nothrow) pl_t;
  if (!pl)
    return nullptr;
  pl->n = n;
  pl->t = 0;
  pl->q = ZZ(0);
  pl->p = ZZ(0);
  pl->r = 0;
  pl->l = 0;
  pl->pk.SetLength(n);
  pl->sighat.SetLength(n);
  return pl;
}

void pl_free(pl_t *pl) {
  if (pl) {
    pl->q.kill();
    pl->p.kill();
    pl->pk.kill();
    pl->sighat.kill();
    delete[] pl->reco_parties;
    pl->sigtilde.kill();
    pl->S.kill();
    delete pl;
  }
}

void pl_print(pl_t *pl) {
  cout << "\n\n___________________________ Public Ledger ___________________________\n";
  cout << pl->n << " participants" << endl;
  cout << "q = " << pl->q << endl;
  cout << "sender_pk : " << pl->pk << endl;
  if (dist) {
    cout << endl << pl->t << " threshold" << endl;
    cout << "encrypted shares :" << endl << pl->sighat << endl;
    pl->ld.print();
    cout << endl;
  }
  if (rec) {
    cout << endl << pl->r << " parties want to reconstruct" << endl;
    cout << "decrypted shares :" << endl;
    for (int i = 0; i < pl->r; i++)
      cout << pl->reco_parties[i] << " ";
    cout << endl << pl->sigtilde << endl;
    int len = pl->dl.size();
    for (int i = 0; i < len; i++) {
      cout << "dleq number " << i << endl;
      pl->dl[i].print();
    }
    cout << "\n\nThe " << pl->l << " secrets are :\n" << pl->S << endl;
  }
  cout << "_____________________________________________________________________" << endl;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// scheme //////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


void lambda(Mat<ZZ_p>& lambs, const int t, pl_t *pl) {
  lambs.SetDims(t,pl->l);
  ZZ_p num;
  ZZ_p den;
  ZZ_p mu;
  ZZ_p tmp;
  ZZ_p invden;
  for (int j = 0; j < pl->l; j++) {
    for (int i = 0; i < t; i++) {
      num = ZZ_p(1); den = ZZ_p(1);
      for (int m = 0; m < t; m++)
        if (m != i) {
          sub(tmp,- ZZ_p(j),ZZ_p(pl->reco_parties[m]));
          mul(num, num, tmp);
          sub(tmp, pl->reco_parties[i], ZZ_p(pl->reco_parties[m]));
          mul(den, den, tmp);
        }
      inv(invden,den);
      mul(mu,num,invden);
      conv(lambs[i][j],mu);
    }
  }
}

clock_t setup(pl_t* pl, Vec<ZZ_p>& sk, const int n, const ZZ& q, const ZZ& p, const ZZ_p& h) {
  // choice of secret keys sk
  ZZ_p s;
  sk.SetLength(n);
  for (int i = 0; i < n; i++) {
    /*random(s);
    while (IsZero(s))
      random(s);*/
    sk[i] = ZZ_p(27 + i);
  }
  // computation of public keys sender_pk = h^sk
  ZZ r;
  ZZ_pPush push(p);
  clock_t time = 0, timetmp;
  for (int i = 0; i < n; i++) {
    r = rep(sk[i]);
    timetmp = clock();
    power(pl->pk[i], h, r);
    time += clock() - timetmp;
  }
  // set the variables in the public ledger
  pl->n = n;
  pl->h = h;
  pl->q = q;
  pl->p = p;
  return time;
}

clock_t distribution(const int l, const int t, const Vec<ZZ_p>& alpha, pl_t *pl) {
  if (!pl || t < 1 || t > pl->n)
    return 0;
  // choice of the polynomial P
  int deg = t + l;
  ZZ_pX P;
  //random(P, deg);
  for (int i = 0; i < deg; i++) {
      SetCoeff(P, i, ZZ_p(11 + i));
  }
  // conputation of the exponents and shamir's shares
  Vec<ZZ_p> s;
  s.SetLength(pl->n+l);
  ZZ_p tmp;
  ZZ repzz;
  clock_t time = 0, timetmp;
  for (int i = -l+1; i <= pl->n; i++) {
    tmp = ZZ_p(i);
    eval(s[i+l-1], P, tmp);
  }
  timetmp = clock();
  time += clock() - timetmp;
  ZZ_pPush push(pl->p);
  // computation of encrypted shares
  for (int i = 0; i < pl->n; i++) {
    repzz = rep(s[i+l]);
    timetmp = clock();
    power(pl->sighat[i],pl->pk[i],repzz);
    time += clock() - timetmp;
  }
  // computation of the proof ldei

  cout << "\n\nHELLO THIS IS BEFORE PROOF!" << endl;
  cout << "q: " << pl->q << endl;
  cout << "p: " << pl->p << endl;
  cout << "pk: " << pl->pk << endl;
  cout << "alpha: " << alpha << endl;
  cout << "deg: " << deg << endl;
  cout << "sighat: " << pl->sighat << endl;
  cout << "p: " << P << endl;
  cout << "LDEI:" << endl;
  pl->ld.print();
  pl->ld.prove(pl->q, pl->p, pl->pk, alpha, deg, pl->sighat, P);
    cout << "\n\nHELLO THIS IS JUST AFTER PROOF!" << endl;
    cout << "q: " << pl->q << endl;
    cout << "p: " << pl->p << endl;
    cout << "pk: " << pl->pk << endl;
    cout << "alpha: " << alpha << endl;
    cout << "deg: " << deg << endl;
    cout << "sighat: " << pl->sighat << endl;
    cout << "p: " << P << endl;
    cout << "LDEI:" << endl;
    pl->ld.print();
  // set the variables in the public ledger
  pl->l = l;
  pl->t = t;
  // clean up
  dist = true;
  s.kill();
  return time;
}

clock_t reconstruction(const int r, pl_t *pl) {
  if (!pl) // error : the public ledger doesn't exist
    return 0;
  int t = pl->n - pl->t;
  if (r < t) // error : not enough parts
    return 0;
  // computation of the Lagrange coefficients
  ZZ_pPush push(pl->q);
  Mat<ZZ_p> lambs;
  clock_t time = 0, timetmp;
  lambda(lambs, t, pl);
  ZZ lamb;
  // copmputation of the secrets
  ZZ_p::init(pl->p);
  pl->S.SetLength(pl->l);
  ZZ_p tmp;
  for (int j = 0; j < pl->l; j++) {
    pl->S[pl->l-j-1] = ZZ_p(1);
    for (int i = 0; i < t; i++) {
      lamb = rep(lambs[i][j]);
      timetmp = clock();
      power(tmp,pl->sigtilde[i],lamb);
      mul(pl->S[pl->l-j-1], pl->S[pl->l-j-1], tmp);
      time += clock() - timetmp;
    }
  }
  // set the variables in the public ledger
  pl->r = r;
  rec = true;
  // clean up
  lambs.kill();
  return time;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// ppvss test //////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

void pvss_test(const int n, const int size) {

  clock_t timetmp, setup_time, dist_time, decrypt_time=0,reco_time, all_time;

  // PARAMETERS
  int k = 128;
  ZZ p,q;
  findprime(q,p,k,size-k);
  int t = n/3;
  int l = n-2*t;
  ZZ_p::init(p);
  ZZ_p gen;
  generator(gen,p);
  ZZ_p h;
  power(h,gen,2);

  // SET UP
  ZZ_p::init(q);
  Vec<ZZ_p> sk;
  rec = clock();
  pl_t * pl = pl_alloc(n);
  if (!pl)
    return;
  setup_time = setup(pl,sk,n,q,p,h);
    // cout << endl << "sk : " << sk << endl;


  // DISTRIBUTION
  Vec<ZZ_p> alpha;
  alpha.SetLength(pl->n);
  for (int i = 0; i < pl->n; i++)
    alpha[i] = ZZ_p(i+1);
  dist_time = distribution(l,t,alpha,pl);

  // VERIFICATION
    cout << "\n\nHELLO THIS IS JUST BEFORE VERIFY!" << endl;
    cout << "q: " << pl->q << endl;
    cout << "p: " << pl->p << endl;
    cout << "pk: " << pl->pk << endl;
    cout << "alpha: " << alpha << endl;
    cout << "deg: " << (t+l) << endl;
    cout << "sighat: " << pl->sighat << endl;
    cout << "LDEI:" << endl;
    pl->ld.print();
  if (!(pl->ld.verify(q, p, pl->pk, alpha, t+l, pl->sighat))) {
    cout << "The proof LDEI isn't correct..." << endl;
    pl_free(pl);
    return;
  }
    cout << "\n\nHELLO THIS IS JUST AFTER VERIFY!" << endl;
    cout << "q: " << pl->q << endl;
    cout << "p: " << pl->p << endl;
    cout << "pk: " << pl->pk << endl;
    cout << "alpha: " << alpha << endl;
    cout << "deg: " << (t+l) << endl;
    cout << "sighat: " << pl->sighat << endl;
    cout << "LDEI:" << endl;
    pl->ld.print();

  // SHARE OF DECRYPTED SHARES AND PROOF DLEQ
  // choice of  the reconstructing parties
  int tab[n];
  int len = n;
  int r = n - t;
  pl->sigtilde.SetLength(r);
  pl->reco_parties = new int[r];
  Vec<ZZ_p> invsk;
  invsk.SetLength(r);
  prng_init(time(nullptr) + getpid());
  for (int i = 0; i < len; i++)
    tab[i] = i;
  for (int i = 0; i < r; i++) {
    int ind = rand() % len;
    int in = tab[ind];
    pl->reco_parties[i] = in + 1;
    inv(invsk[i],sk[in]);
    len--;
    for (int j = ind; j < len; j++)
      tab[j] = tab[j+1];
  }
  // computations
  ZZ_p::init(p);
  Mat<ZZ_p> g;
  g.SetDims(r,2);
  Mat<ZZ_p> x;
  x.SetDims(r,2);
  int id;
  for (int i = 0; i < r; i++) {
    id = pl->reco_parties[i];
    x[i][0] = h;
    g[i][1] = pl->sighat[id-1];
    timetmp = clock();
    power(x[i][1],g[i][1],rep(invsk[i]));
    decrypt_time += clock() - timetmp;
    pl->sigtilde[i] = x[i][1];
    g[i][0]= pl->pk[id-1];
    pl->dl.emplace_back();
    pl->dl[i].prove(q,p,g[i],x[i],invsk[i]);
  }
  invsk.kill();

  // VERIFICATION OF PROOF DLEQ
  for (int i = 0; i < r; i ++) {
    if(!pl->dl[i].verify(q,p,g[i],x[i])) {
      cout << "At least one of the proofs DLEQ isn't correct..." << endl;
      pl_free(pl);
      return;
    }
  }

  // RECONSTRUCTION
  reco_time = reconstruction(r, pl);
  // pl_print(pl);

  // RECONSTRUCTINO VERIFICATION
  ZZ_p::init(q);
  Vec<ZZ_p> alphaverif;
  alphaverif.SetLength(r+l);
  for (int j = 0; j < l; j++)
    alphaverif[j] = ZZ_p(j-l+1);
  for (int j = l; j < r+l; j++)
    alphaverif[j] = pl->reco_parties[j-l];
  ZZ_p::init(p);
  Vec<ZZ_p> xverif;
  xverif.SetLength(r+l);
  for (int j = 0; j < l; j++) {
    xverif[j] = pl->S[j];
  }
  for (int j = l; j < r+l; j++) {
    xverif[j] = pl->sigtilde[j-l];
  }
  if (!(localldei(q,p,alphaverif,t+l,xverif,r+l))) {
    cout << "The reconstruction isn't correct..." << endl;
    pl_free(pl);
    return;
  }

  all_time = setup_time + dist_time + decrypt_time + reco_time;

  // CLEAN UP
  pl_free(pl);

  // TIME
  cout << "\n\ntimes for q of " << size << " bits and " << n << " participants in finite field:\n\n";
  cout << "time for setting up: " << (float)setup_time/CLOCKS_PER_SEC << "s" << endl;
  cout << "time for distributing: " << (float)dist_time/CLOCKS_PER_SEC << "s" << endl;
  cout << "time for sharing decrypted shares with dleq: " << (float)decrypt_time/CLOCKS_PER_SEC << "s" << endl;
  cout << "time for reconstructing the secrets: " << (float)reco_time/CLOCKS_PER_SEC << "s" << endl;
  cout << "\nglobal time: " << (float)all_time/CLOCKS_PER_SEC << "s\n\n";
  cout << "here we only timed elementary operations and we didn't timed the proofs\n\n";
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////// ALBATROSS IMPL //////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

int n; // number of participants
int t; // threshold
int l; // number of secrets
int r; // number of participants who want to reconstruct the secrets
ZZ q; // order of the group G_q
ZZ p; // p = 2q+1
ZZ_p h; // generator of G_q

struct LedgerMessage {
    ZZ_p sender_pk; // id of the party who posted this on the ledger
    ZZ_p recipient_pk; // id of intended receiver (-1 if none)
    int type; // 0: sender_pk, 1: enc. share, 2: LDEI.a, 3: LDEI.e, 4: LDEI.z, 5: sharing polynomial
    ZZ_p value;

    LedgerMessage(const ZZ_p &_sender_pk, const ZZ_p &_recipient_pk, int _type, const ZZ_p &_value) {
        sender_pk = _sender_pk;
        recipient_pk = _recipient_pk;
        type = _type;
        value = _value;
    }

    LedgerMessage(const ZZ_p &_sender_pk, int _type, const ZZ_p &_value) {
        sender_pk = _sender_pk;
        recipient_pk = ZZ_p(0);
        type = _type;
        value = _value;
    }
};


// has to be static global in order for it to work right now.
// works as a temporary list to fetch database results to.
static vector<LedgerMessage> messages_db;

class Ledger {

private:
    vector<LedgerMessage> messages; // replace this with db
public:
    Ledger() = default;

    // TODO find correct place for helper methods
    string ZZ_p_to_string(const ZZ_p &z) {
        stringstream buffer;
        buffer << z;
        return buffer.str();
    }

    static ZZ_p string_to_ZZ_p(string s) {
        ZZ_p z;
        z = to_ZZ_p(conv<ZZ>(s.c_str()));
        return z;
    }

    void post_to_ledger(LedgerMessage lm) {
        messages.push_back(lm);
    }

    vector<LedgerMessage> get_all_messages() {
        return messages; //replace this with db
    }

    vector<LedgerMessage> get_messages_with_sender_pk(const ZZ_p &sender_pk) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.sender_pk == sender_pk) {
                results.emplace_back(message);
            }
        }
        return results;
    }

    vector<LedgerMessage> get_messages_with_recipient_pk(const ZZ_p &recipient_pk) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.recipient_pk == recipient_pk) {
                results.emplace_back(message);
            }
        }
        return results;
    }

    vector<LedgerMessage> get_messages_with_type(int _type) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.type == _type) {
                results.emplace_back(message);
            }
        }
        return results;
    }

    vector<LedgerMessage> get_ldei_messages(const ZZ_p &sender_pk) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.sender_pk == sender_pk && message.type >= 2 && message.type <= 4) {
                results.emplace_back(message);
            }
        }
        return results;
    }

    vector<LedgerMessage> get_messages_with_sender_pk_type(const ZZ_p &sender_pk, int type) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.sender_pk == sender_pk && message.type == type) {
                results.emplace_back(message);
            }
        }
        return results;
    }

};

Ledger ledger;


/*int sender_pk;
Vec<ZZ_p> pk_all;
ZZ_p sk;
ZZ_p sender_pk;
ZZ_pX P;
Vec<ZZ_p> sighat;
LDEI ld;
vector<int> c; // set of parties who have posted a valid sharing*/

void generate_secret_key(ZZ_p &sk) {
    random(sk);
    while (IsZero(sk))
        random(sk);
}

void generate_public_key(const ZZ_p& sk, ZZ_p &pk) {
    power(pk, h, rep(sk));
}

void read_all_public_keys(Vec<ZZ_p> &pk_list) {
    pk_list.SetLength(n);
    vector<LedgerMessage> pk_messages = ledger.get_messages_with_type(0);

    for (int i = 0; i < pk_messages.size(); i++) {
        pk_list[i] = pk_messages[i].value;
    }
}

void post_encrypted_shares_to_ledger(const ZZ_p &sender_pk, const Vec<ZZ_p> &pk_all, const Vec<ZZ_p> &sighat) {
    for (int i = 0; i < n; i++) {
        ledger.post_to_ledger(LedgerMessage(sender_pk, pk_all[i], 1, sighat[i]));
    }
}

void read_encrypted_shares_from_ledger(const ZZ_p &sender_pk, Vec<ZZ_p> &sighat) {
    sighat.SetLength(n);
    vector<LedgerMessage> msg = ledger.get_messages_with_sender_pk_type(sender_pk, 1);
    for (int j = 0; j < msg.size(); j++) {
        sighat[j] = msg[j].value;
    }
}

void post_ldei_to_ledger(const LDEI &ld, const ZZ_p &sender_pk) {
    for (int i = 0; i < ld.a.length(); i++) {
        ledger.post_to_ledger(LedgerMessage(sender_pk, 2, ld.a[i]));
    }
    ledger.post_to_ledger(LedgerMessage(sender_pk, 3, ld.e));
    for (int i = 0; i < deg(ld.z) + 1; i++) {
        ledger.post_to_ledger(LedgerMessage(sender_pk, 4, coeff(ld.z, i)));
    }
}

LDEI read_LDEI_from_ledger(const ZZ_p &sender_pk) {
    int ai = 0, zi = 0; // indices
    vector<LedgerMessage> ldei_messages = ledger.get_ldei_messages(sender_pk);
    Vec<ZZ_p> a;
    a.SetLength(n);
    ZZ_p e;
    ZZ_pX z;
    for (const auto& lm : ldei_messages) {
        if (lm.type == 2) {
            a[ai++] = lm.value;
        } else if (lm.type == 3) {
            e = lm.value;
        } else {
            SetCoeff(z, zi++, lm.value);
        }
    }
    return LDEI(a, e, z);
}

ZZ_pX generate_random_polynomial(int deg) {
    ZZ_pX pol;
    random(pol, deg);
    return pol;
}

void distribution_alb(const ZZ_pX &P, const Vec<ZZ_p> &pk_all, Vec<ZZ_p> &sighat, LDEI &ld) {
    if (t < 1 || t > n)
        return;
    // conputation of the exponents and shamir's shares
    Vec<ZZ_p> s;
    s.SetLength(n+l);
    ZZ_p tmp;
    ZZ repzz;
    clock_t time = 0, timetmp;
    for (int i = -l+1; i <= n; i++) {
        tmp = ZZ_p(i);
        eval(s[i + l - 1], P, tmp);
    }

    timetmp = clock();
    time += clock() - timetmp;
    ZZ_pPush push(p);
    // computation of encrypted shares
    for (int i = 0; i < n; i++) {
        repzz = rep(s[i+l]);
        timetmp = clock();
        power(sighat[i], pk_all[i], repzz);
        time += clock() - timetmp;
    }

    // computation of the proof ldei
    Vec<ZZ_p> alpha;
    alpha.SetLength(n);
    for (int i = 0; i < n; i++) {
        alpha[i] = ZZ_p(i + 1);
    }

    ld.prove(q, p, pk_all, alpha, t + l, sighat, P);
    // clean up
    s.kill();
}

void verify_ldei(const Vec<ZZ_p> &alpha, const Vec<ZZ_p> &pk_all, vector<ZZ_p> &valid_sharings_pids) {
    for (int i = 0; i < n; i++) {
        LDEI ldei = read_LDEI_from_ledger(pk_all[i]);
        //cout << "now verifying ldei for pk = " << pk_all[i] << endl;
        Vec<ZZ_p> sighat;
        read_encrypted_shares_from_ledger(pk_all[i], sighat);
        //if (ldei.verify(q, p, pk_all, alpha, t+l, sighat)) {
            valid_sharings_pids.emplace_back(pk_all[i]);
        //}
    }
}

void post_sharing_polynomial_to_ledger(const ZZ_p &sender_pk, ZZ_pX &pol) {
    for (int i = 0; i < t + l; i++) {
        ledger.post_to_ledger(LedgerMessage(sender_pk, 5, coeff(pol, i)));
    }
}

void read_sharing_polynomial_from_ledger(const ZZ_p &sender_pk, ZZ_pX &polynomial) {
    int index = 0;
    for (const LedgerMessage& lm: ledger.get_messages_with_sender_pk_type(sender_pk, 5)) {
        SetCoeff(polynomial, index++, lm.value);
    }
}

void verify_sharing_polynomials(const vector<ZZ_p> &valid_sharings_pks, const Vec<ZZ_p> &pk_all, vector<ZZ_p> &invalid_sharing_polynomials_pks) {
    for (const ZZ_p& pk : valid_sharings_pks) {
        ZZ_pX polynomial;
        read_sharing_polynomial_from_ledger(pk, polynomial);
        Vec<ZZ_p> sighat;
        sighat.SetLength(n);
        LDEI ld;
        distribution_alb(polynomial, pk_all, sighat, ld);
        //LDEI posted_ldei = read_LDEI_from_ledger(pk);
        Vec<ZZ_p> posted_sighat;
        read_encrypted_shares_from_ledger(pk, posted_sighat);
        cout << "the posted sighat was: " << posted_sighat << endl;
        cout << "the reproduced sighat is: " << sighat << endl;
        //cout << "the posted LDEI was:" << endl;
        //posted_ldei.print();
        //cout << "the reproduced LDEI is:" << endl;
        //ld.print();
        if (sighat != posted_sighat) {
            cout << "pk " << pk << " has not opened their secrets correctly" << endl;
            invalid_sharing_polynomials_pks.emplace_back(pk);
        }
    }
}

void alb_test_all(const int _n, const int size) {
    // PARAMETERS (global parameters for everybody)
    n = _n;
    int k = 128;
    findprime(q, p, k, size - k);
    t = n / 3;
    l = n - 2 * t;
    ZZ_p::init(p);
    ZZ_p gen;
    generator(gen, p);
    power(h, gen, 2);

    alb_test(_n, size);

}

struct party_data {
    ZZ_p sk;
    ZZ_p pk;
    Vec<ZZ_p> pk_all;
    ZZ_pX polynomial;
    Vec<ZZ_p> sighat;
    LDEI ld;
    vector<ZZ_p> c; // set of parties who posted valid sharings
    vector<ZZ_p> c_a; // set of parties in c who did not open secrets correctly

    party_data() {
        pk_all.SetLength(n);
        sighat.SetLength(n);
    }
};

vector<party_data> party;

/*int sender_pk;
Vec<ZZ_p> pk_all;
ZZ_p sk;
ZZ_p sender_pk;
ZZ_pX P;
Vec<ZZ_p> sighat;
LDEI ld;
vector<int> c; // set of parties who have posted a valid sharing*/

void alb_test(const int _n, const int size) {

    for (int i = 0; i < n; i++) {
        party.emplace_back(party_data());
    }

    for (int i = 0; i < n; i++) {
        // SET UP
        generate_secret_key(party[i].sk);
        //party[i].sk = ZZ_p(27324 + i);
        generate_public_key(party[i].sk, party[i].pk);
        cout << "party " << i << ": my pk is " << party[i].pk << endl;
        ledger.post_to_ledger(LedgerMessage(party[i].pk, 0, party[i].pk));
    }

    // TODO wait for everyone to post their sender_pk
    /*while (ledger.get_messages_with_type(0).size() < n) {
        cout << "party-" << sender_pk << ": I am waiting" << endl;
    }*/


    for (int i = 0; i < n; i++) {
        cout << i << endl;
        // Read everyone's public keys
        read_all_public_keys(party[i].pk_all);
        cout << "everyone's public keys: " << party[i].pk_all << endl;
        party[i].polynomial = generate_random_polynomial(t + l);
        cout << "party " << i << " (pk " << party[i].pk << "): my polynomial is " << party[i].polynomial << endl;
        distribution_alb(party[i].polynomial, party[i].pk_all, party[i].sighat, party[i].ld);
        post_encrypted_shares_to_ledger(party[i].pk, party[i].pk_all, party[i].sighat);
        /*cout << "my encrypted shares are " << endl;
        for (int j = 0; j < n; j++) {
            cout << party[i].sighat[j] << endl;
        }*/
        post_ldei_to_ledger(party[i].ld, party[i].pk);
        cout << endl << endl;
    }

    cout << "Distribution done" << endl;

    // TODO wait for everyone (not everyone?) to post encrypted shares + LDEI

    for (int i = 0; i < n; i++) {
        cout << i << endl;
        Vec<ZZ_p> alpha;
        alpha.SetLength(n);
        for (int j = 0; j < n; j++) {
            alpha[j] = ZZ_p(j + 1);
        }
        verify_ldei(alpha, party[i].pk_all, party[i].c);
        if (party[i].c.size() < n - t) {
            cout << "oh no not enough parties posted valid sharings" << endl;
            return;
        }
        cout << "c is size " << party[i].c.size() << endl;
    }

    for (int i = 0; i < n; i++) {
        post_sharing_polynomial_to_ledger(party[i].pk, party[i].polynomial);
    }

    for (int i = 0; i < n; i++) {
        verify_sharing_polynomials(party[i].c, party[i].pk_all, party[i].c_a);
        cout << "c_a size: " << party[i].c_a.size() << endl;
        // TODO if c_a.size() > 0, reconstruct!


    }


}