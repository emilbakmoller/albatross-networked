/* implementation of pvss protocol */
#include <iostream>
#include <cstdlib>
#include <ctime>
#include <unistd.h>
#include <utility>
#include <vector>
#include <sstream>

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
  Vec<ZZ_p> sighat; // encrypted shares  Map<pk, Vec<ZZ_p>>
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
  cout << "pk : " << pl->pk << endl;
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
    random(s);
    while (IsZero(s))
      random(s);
    sk[i] = s;
  }
  // computation of public keys pk = h^sk
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
  random(P, deg);
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
  pl->ld.prove(pl->q, pl->p, pl->pk, alpha, deg, pl->sighat, P);
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
  if (!(pl->ld.verify(q, p, pl->pk, alpha, t+l, pl->sighat))) {
    cout << "The proof LDEI isn't correct..." << endl;
    pl_free(pl);
    return;
  }

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
    int pid; // id of the party who posted this on the ledger
    int rid; // id of intended receiver (-1 if none)
    int type; // 0: pk, 1: enc. share, 2: LDEI.a, 3: LDEI.e, 4: LDEI.z, 5: sharing polynomial
    ZZ_p value;

    LedgerMessage(int _pid, int _rid, int _type, const ZZ_p &_value) {
        pid = _pid;
        rid = _rid;
        type = _type;
        value = _value;
    }

    LedgerMessage(int _pid, int _type, const ZZ_p &_value) {
        pid = _pid;
        rid = -1;
        type = _type;
        value = _value;
    }
};


// has to be static global in order for it to work right now
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

    static int callback(void *NotUsed, int argc, char **argv, char **azColName) {
        int i;
        for(i = 0; i<argc; i++) {
            printf("%s = %s\n", azColName[i], argv[i] ? argv[i] : "NULL");
        }
        printf("\n");
        return 0;
    }


    // callback used when we want to save multiple results from the database in a list.
    // right now the list is erased with every call to the database.
    static int callback_message_list(void *NotUsed, int argc, char **argv, char **azColName) {

        string lol = argv[3];

        ZZ_p test = string_to_ZZ_p(lol);


        // update and make it use real parameters
        LedgerMessage m = LedgerMessage(1,2,3,test);

        messages_db.emplace_back(m);

        printf("\n");

        return 0;
    }

    void insert_message(LedgerMessage lm) {
        sqlite3 *db;
        char *zErrMsg = 0;
        int rc;
        char *sql;

        rc = sqlite3_open("database", &db);

        if( rc ) {
            fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        } else {
            //fprintf(stderr, "Opened database successfully\n");
        }


        std::string query = "INSERT INTO LEDGER (PID, RID, TYPE, VALUE) VALUES("+std::to_string(lm.pid)+", "+std::to_string(lm.rid)+" , "+std::to_string(lm.type)+",'"+ZZ_p_to_string(lm.value)+"')";

        sql = &query[0];

        rc = sqlite3_exec(db, sql, callback, 0, &zErrMsg);

        if( rc != SQLITE_OK ){
            fprintf(stderr, "SQL error: %s\n", zErrMsg);
            sqlite3_free(zErrMsg);
        } else {
            //fprintf(stdout, "Records created successfully\n");
        }
        sqlite3_close(db);
    }

    void create_database() {
        // TODO figure out if the variables can be global
        sqlite3 *db;
        char *zErrMsg = 0;
        int rc;

        std::cout << "Creating database: " << std::endl;

        rc = sqlite3_open("database", &db);

        if( rc ) {
            fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        } else {
            fprintf(stderr, "Opened database successfully\n");
        }
        sqlite3_close(db);
    }

    void create_table() {
        sqlite3 *db;
        char *zErrMsg = 0;
        int rc;
        char *sql;

        std::cout << "Creating table in database: database"  << std::endl;


        //name of database to connect to
        rc = sqlite3_open("database", &db);

        if( rc ) {
            fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        } else {
            fprintf(stdout, "Opened database successfully\n");
        }

        // TODO change PID to be unique
        sql = "DROP TABLE IF EXISTS LEDGER; CREATE TABLE LEDGER("  \
      "PID INT      NOT NULL," \
      "RID           INT    NOT NULL," \
      "TYPE            INT     NOT NULL," \
      "VALUE        CHAR(100));";

        /* Execute SQL statement */
        rc = sqlite3_exec(db, sql, callback, 0, &zErrMsg);


        if( rc != SQLITE_OK ){
            fprintf(stderr, "SQL error: %s\n", zErrMsg);
            sqlite3_free(zErrMsg);
        } else {
            fprintf(stdout, "Table created successfully\n");
        }
        sqlite3_close(db);
    }

    // does not currently save the results, only prints it.
    void get_all_messages_db() {
        sqlite3 *db;
        char *zErrMsg = 0;
        int rc;
        char *sql;
        const char* data = "Callback function called";

        rc = sqlite3_open("database", &db);

        if( rc ) {
            fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        } else {
            fprintf(stderr, "Opened database successfully\n");
        }

        std::string query = "SELECT * from LEDGER";

        // convert from string to sql
        sql = &query[0];

        /* Execute SQL statement */
        rc = sqlite3_exec(db, sql, callback, (void*)data, &zErrMsg);

        if( rc != SQLITE_OK ) {
            fprintf(stderr, "SQL error: %s\n", zErrMsg);
            sqlite3_free(zErrMsg);
        } else {
            fprintf(stdout, "Operation done successfully\n");
            //cout << data << endl;
        }
        sqlite3_close(db);

    }

    void get_messages_with_pid_db(int _pid) {
        sqlite3 *db;
        char *zErrMsg = 0;
        int rc;
        char *sql;
        const char* data = "Callback function called";

        rc = sqlite3_open("database", &db);

        if( rc ) {
            fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        } else {
            fprintf(stderr, "Opened database successfully\n");
        }

        std::string query = "SELECT * from LEDGER WHERE PID = " +std::to_string(_pid)+"";

        // convert from string to sql
        sql = &query[0];

        cout << sql << endl;;

        /* Execute SQL statement */
        rc = sqlite3_exec(db, sql, callback_message_list, (void*)data, &zErrMsg);

        if( rc != SQLITE_OK ) {
            fprintf(stderr, "SQL error: %s\n", zErrMsg);
            sqlite3_free(zErrMsg);
        } else {
            fprintf(stdout, "Operation done successfully\n");
            //cout << data << endl;
        }
        sqlite3_close(db);

    }

    void post_to_ledger(LedgerMessage lm) {
        messages.push_back(lm);
        // insert into database
        insert_message(lm);
    }

    vector<LedgerMessage> get_all_messages() {
        // figure out how to convert back into LedgerMessage from database
        cout << "calling get_all_messages" << endl;
        get_all_messages_db();
        return messages; //replace this with db
    }

    vector<LedgerMessage> get_messages_with_pid(int _pid) {
        // we clear the global list with messages from the ledger
        messages_db.clear();
        get_messages_with_pid_db(_pid);
        return messages_db;
    }

    vector<LedgerMessage> get_messages_with_rid(int _rid) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.rid == _rid) {
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

    vector<LedgerMessage> get_ldei_messages(int _pid) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.pid == _pid && message.type >= 2 && message.type <= 4) {
                results.emplace_back(message);
            }
        }
        return results;
    }

    vector<LedgerMessage> get_messages_with_pid_type(int _pid, int _type) {
        vector<LedgerMessage> results;
        for (auto & message : messages) {
            if (message.pid == _pid && message.type == _type) {
                results.emplace_back(message);
            }
        }
        return results;
    }

};

Ledger ledger;
int pid;
Vec<ZZ_p> pk_all;
ZZ_p sk;
ZZ_p pk;
ZZ_pX P;
Vec<ZZ_p> sighat;
LDEI ld;
vector<int> c; // set of parties who have posted a valid sharing

ZZ_p generate_secret_key() {
    ZZ_p sk;
    random(sk);
    while (IsZero(sk))
        random(sk);
    return sk;
}

ZZ_p generate_public_key(ZZ_p sk) {
    ZZ_p pk;
    power(pk, h, rep(sk));
    return pk;
}

Vec<ZZ_p> read_all_public_keys() {
    Vec<ZZ_p> pk_all;
    pk_all.SetLength(n);
    vector<LedgerMessage> pk_messages = ledger.get_messages_with_type(0);
    for (int i = 0; i < pk_messages.size(); i++) {
        pk_all[i] = pk_messages[i].value;
    }
    return pk_all;
}

void post_encrypted_shares_to_ledger() {
    for (int i = 0; i < n; i++) {
        ledger.post_to_ledger(LedgerMessage(pid, i, 1, sighat[i]));
    }
}

void post_ldei_to_ledger() {
    for (int i = 0; i < ld.a.length(); i++) {
        ledger.post_to_ledger(LedgerMessage(pid, 2, ld.a[i]));
    }
    ledger.post_to_ledger(LedgerMessage(pid, 3, ld.e));
    for (int i = 0; i < deg(ld.z); i++) {
        ledger.post_to_ledger(LedgerMessage(pid, 4, coeff(ld.z, i)));
    }
}

LDEI read_LDEI_from_ledger(int pid) {
    int ai = 0, zi = 0; // indices
    vector<LedgerMessage> ldei_messages = ledger.get_ldei_messages(pid);
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


void distribution_alb(const Vec<ZZ_p>& alpha, int pid) {
    if (t < 1 || t > n)
        return;
    // choice of the polynomial P
    int deg = t + l;
    random(P, deg);
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
        //cout << "sighat: " << sighat[i] << endl;
        time += clock() - timetmp;
    }

    post_encrypted_shares_to_ledger();

    // computation of the proof ldei
    ld.prove(q, p, pk_all, alpha, deg, sighat, P);
    ld.print();
    // set the variables in the public ledger
    post_ldei_to_ledger();
    // clean up
    s.kill();
}

vector<int> verify_ldei(Vec<ZZ_p> alpha) {
    vector<int> valid_sharings_pids;
    for (int i = 0; i < n; i++) {
        LDEI ldei = read_LDEI_from_ledger(i);
        if (ldei.verify(q, p, pk_all, alpha, t+l, sighat)) {
            valid_sharings_pids.emplace_back(i);
        }
    }
    return valid_sharings_pids;
}

void post_sharing_polynomial_to_ledger() {
    for (int i = 0; i < t + l; i++) {
        ledger.post_to_ledger(LedgerMessage(pid, 5, coeff(P, i)));
    }
}

void verify_sharing_polynomials() {
    for (int pid : c) {
        ZZ_pX polynomial;
        int index = 0;
        for (const LedgerMessage& lm: ledger.get_messages_with_pid_type(pid, 5)) {
            SetCoeff(polynomial, index++, lm.value);
        }
        // TODO reproduce distribution phase for this party
    }
}

void alb_test(const int _n, const int size) {


    // setup db and override it every execution
    ledger.create_database();
    ledger.create_table();

    int pid = 0; // how do I know this????

    // PARAMETERS
    n = _n;
    int k = 128;
    findprime(q, p, k, size - k);
    t = n / 3;
    l = n - 2 * t;
    ZZ_p::init(p);
    ZZ_p gen;
    generator(gen, p);
    power(h, gen, 2);
    sighat.SetLength(n);

    // SET UP
    sk = generate_secret_key();
    pk = generate_public_key(sk);
    ledger.post_to_ledger(LedgerMessage(pid, 0, pk));

    cout << "Posted to ledger" << endl;

    // TODO wait for everyone to post their pk

    // Read everyone's public keys
    pk_all = read_all_public_keys();

    // DISTRIBUTION
    Vec<ZZ_p> alpha;
    alpha.SetLength(n);
    for (int j = 0; j < n; j++) {
        alpha[j] = ZZ_p(j + 1);
    }
    distribution_alb(alpha, pid);

    cout << "Distribution done" << endl;

    //ledger.get_all_messages_db();


    // get all messages with pid = 0, maybe create function to display
    ledger.get_messages_with_pid_db(0);

    // TODO wait for everyone (not everyone?) to post encrypted shares + LDEI

/*    c = verify_ldei(alpha);
    if (c.size() < n - t) {
        cout << "oh no not enough parties posted valid sharings" << endl;
        return;
    }


    post_sharing_polynomial_to_ledger();*/

    //ledger.get_all_messages_db();

    //verify_sharing_polynomials();


}