// https://www.codingame.com/ide/puzzle/nintendo-sponsored-contest (been trying to solve this for a year now)

#include <bits/stdc++.h>
using namespace std;

struct Poly {
    vector<uint64_t> w; // little-endian words; bit i => w[i/64] bit (i%64)
    Poly() {}
    Poly(size_t words) : w(words, 0) {}
    void ensure(size_t words) { if (w.size() < words) w.resize(words, 0); }
    void trim() {
        while (!w.empty() && w.back() == 0) w.pop_back();
    }
    bool is_zero() const {
        for (auto x: w) if (x) return false;
        return true;
    }
    int deg() const {
        for (int i = (int)w.size() - 1; i >= 0; --i) {
            uint64_t v = w[i];
            if (v) return i*64 + 63 - __builtin_clzll(v);
        }
        return -1;
    }
    bool get_bit(int i) const {
        int wi = i >> 6;
        int bi = i & 63;
        if (wi >= (int)w.size()) return false;
        return (w[wi] >> bi) & 1ull;
    }
    void set_bit(int i) {
        int wi = i >> 6;
        int bi = i & 63;
        ensure(wi+1);
        w[wi] |= (1ull << bi);
    }
    void clear() { fill(w.begin(), w.end(), 0); }
    void xor_shifted(const Poly &other, int shift) {
        // this ^= (other << shift)
        if (other.w.empty()) return;
        int word_shift = shift >> 6;
        int bit_shift = shift & 63;
        ensure(other.w.size() + word_shift + (bit_shift ? 1 : 0));
        if (bit_shift == 0) {
            for (size_t i=0;i<other.w.size();++i) w[i+word_shift] ^= other.w[i];
        } else {
            for (size_t i=0;i<other.w.size();++i) {
                uint64_t lo = other.w[i] << bit_shift;
                uint64_t hi = other.w[i] >> (64 - bit_shift);
                w[i + word_shift] ^= lo;
                w[i + word_shift + 1] ^= hi;
            }
        }
    }
    Poly shifted(int shift) const {
        Poly r;
        if (is_zero()) return r;
        int word_shift = shift >> 6;
        int bit_shift = shift & 63;
        r.w.assign(w.size() + word_shift + (bit_shift?1:0), 0);
        if (bit_shift==0) {
            for (size_t i=0;i<w.size();++i) r.w[i+word_shift] = w[i];
        } else {
            for (size_t i=0;i<w.size();++i) {
                r.w[i+word_shift] ^= (w[i] << bit_shift);
                r.w[i+word_shift+1] ^= (w[i] >> (64-bit_shift));
            }
        }
        r.trim();
        return r;
    }
    // XOR another poly into this
    void xor_with(const Poly &o) {
        ensure(o.w.size());
        for (size_t i=0;i<o.w.size();++i) w[i] ^= o.w[i];
    }
};

// full multiply (no reduction) using iterate set-bits of a
Poly mul_full(const Poly &a, const Poly &b) {
    if (a.is_zero() || b.is_zero()) return Poly();
    Poly r;
    r.w.assign(a.w.size() + b.w.size(), 0);
    for (size_t i = 0; i < a.w.size(); ++i) {
        uint64_t av = a.w[i];
        while (av) {
            uint64_t lsb = av & -av;
            int bit = __builtin_ctzll(av);
            int pos = (int)i*64 + bit;
            // XOR b shifted by pos
            int word_shift = pos >> 6;
            int bit_shift = pos & 63;
            if (bit_shift == 0) {
                for (size_t j=0;j<b.w.size();++j) r.w[j+word_shift] ^= b.w[j];
            } else {
                for (size_t j=0;j<b.w.size();++j) {
                    r.w[j+word_shift] ^= (b.w[j] << bit_shift);
                    r.w[j+word_shift+1] ^= (b.w[j] >> (64-bit_shift));
                }
            }
            av ^= lsb;
        }
    }
    r.trim();
    return r;
}

// polynomial division a / b -> quotient q and remainder r (over GF(2))
// works with 64-bit words; b must not be zero.
pair<Poly,Poly> divmod_poly(Poly a, const Poly &b) {
    Poly q;
    a.trim();
    int db = b.deg();
    if (db == -1) return {q, a};
    int da = a.deg();
    if (da < db) return {q, a};
    q.w.assign((da - db) / 64 + 1 + 1, 0);
    // We will repeatedly align b to the leading bit of a and xor.
    while (true) {
        a.trim();
        da = a.deg();
        if (da < db) break;
        int shift = da - db;
        // XOR b << shift into a
        int word_shift = shift >> 6;
        int bit_shift = shift & 63;
        // ensure a has enough words
        a.ensure(max(a.w.size(), b.w.size() + word_shift + (bit_shift?1:0)));
        if (bit_shift == 0) {
            for (size_t i=0;i<b.w.size();++i) a.w[i+word_shift] ^= b.w[i];
        } else {
            for (size_t i=0;i<b.w.size();++i) {
                uint64_t lo = b.w[i] << bit_shift;
                uint64_t hi = b.w[i] >> (64 - bit_shift);
                a.w[i + word_shift] ^= lo;
                a.w[i + word_shift + 1] ^= hi;
            }
        }
        // set quotient bit
        int qwi = shift >> 6;
        int qbi = shift & 63;
        q.ensure(qwi+1);
        q.w[qwi] |= (1ull << qbi);
    }
    a.trim(); q.trim();
    return {q, a};
}

Poly gcd_poly(Poly a, Poly b) {
    a.trim(); b.trim();
    if (a.is_zero()) return b;
    if (b.is_zero()) return a;
    while (!b.is_zero()) {
        Poly r = divmod_poly(a, b).second;
        a = move(b);
        b = move(r);
    }
    return a;
}

// compute x^(2*i) mod f by starting cur=1 and repeatedly squaring (which is same as multiply by x^2)
// We implement step as: cur <<= 2; reduce by f via divmod
void berlekamp_factor_rec(const Poly &f_in, vector<Poly> &out);

void berlekamp_factor(const Poly &f, vector<Poly> &out) {
    if (f.is_zero()) return;
    if (f.deg() <= 0) { out.push_back(f); return; }
    berlekamp_factor_rec(f, out);
}

void berlekamp_factor_rec(const Poly &f_in, vector<Poly> &out) {
    Poly f = f_in; f.trim();
    int n = f.deg();
    if (n <= 1) { out.push_back(f); return; }
    // remove x factor if present (constant term 0)
    if (f.get_bit(0) == 0) {
        // factor out x while possible
        Poly cur = f;
        int count = 0;
        while (cur.get_bit(0) == 0) {
            // divide by x: shift right by 1
            Poly nxt; nxt.w.assign(max(1, (int)cur.w.size()), 0);
            for (int i = 1; i <= cur.deg(); ++i) if (cur.get_bit(i)) {
                int wi = (i-1) >> 6; int bi = (i-1)&63;
                nxt.ensure(wi+1);
                nxt.w[wi] |= (1ull << bi);
            }
            cur = move(nxt);
            cur.trim();
            count++;
            if (cur.is_zero()) break;
        }
        for (int i=0;i<count;++i) {
            Poly xpoly(1); xpoly.w[0]=2; // x
            out.push_back(xpoly);
        }
        if (cur.is_zero()) return;
        f = move(cur);
        if (f.deg() <= 1) { out.push_back(f); return; }
    }

    n = f.deg();
    // Build matrix Q where col i is coefficients of x^{2*i} mod f for i=0..n-1
    // We'll store N = Q - I (n x n) as vector<vector<uint64_t>> rows (bitset size n)
    int words = (n + 63) >> 6;
    vector<vector<uint64_t>> mat(n, vector<uint64_t>(words, 0ULL));

    // cur = 1
    Poly cur( (n+64)/64 ); cur.w.assign(cur.w.size(),0); cur.set_bit(0);
    // square by shifting bits left by factor 2: but implement as shift left by 2 then reduce
    for (int i=0;i<n;++i) {
        // fill column i with cur's low n bits
        for (int bit = 0; bit <= cur.deg() && bit < n; ++bit) {
            if (cur.get_bit(bit)) {
                int wi = bit >> 6, bi = bit & 63;
                mat[bit][i>>6] |= (1ull << (i & 63)); // WRONG placement — we instead want mat[row][col]
            }
        }
        // Wait — above was mistaken orientation. We'll instead fill transposed: for row r, set mat[r][i] = cur[r]
        for (int r=0;r<n;++r) {
            if (cur.get_bit(r)) mat[r][i>>6] |= (1ull << (i & 63));
        }
        // cur <<= 2  and reduce mod f
        Poly shifted; shifted.w.assign(cur.w.size()+1,0);
        // shift by 2
        int word_shift = 2 >> 6; int bit_shift = 2 & 63;
        if (bit_shift==0) {
            for (size_t wi=0;wi<cur.w.size();++wi) shifted.w[wi+word_shift] = cur.w[wi];
        } else {
            for (size_t wi=0;wi<cur.w.size();++wi) {
                shifted.w[wi+word_shift] ^= (cur.w[wi] << bit_shift);
                shifted.w[wi+word_shift+1] ^= (cur.w[wi] >> (64-bit_shift));
            }
        }
        shifted.trim();
        // reduce shifted mod f
        Poly rem = divmod_poly(shifted, f).second;
        cur = move(rem);
    }

    // Build N = Q - I (toggle diagonal)
    for (int r=0;r<n;++r) {
        // toggle diagonal bit at column r
        int col = r;
        int wi = col>>6, bi = col&63;
        mat[r][wi] ^= (1ull<<bi);
    }

    // Gaussian elimination on mat to find nullspace: mat * v = 0
    // We'll do row-reduction and record pivot positions
    vector<int> pivot_col(n, -1);
    int row = 0;
    for (int col = 0; col < n && row < n; ++col) {
        // find row with bit col set at or below 'row'
        int sel = -1;
        for (int r=row;r<n;++r) {
            int wi = col>>6; int bi = col&63;
            if ( (mat[r][wi] >> bi) & 1ULL ) { sel = r; break; }
        }
        if (sel == -1) continue;
        swap(mat[sel], mat[row]);
        pivot_col[row] = col;
        // eliminate other rows
        for (int r=0;r<n;++r) if (r!=row) {
            int wi = col>>6; int bi = col&63;
            if ( (mat[r][wi] >> bi) & 1ULL ) {
                // row r ^= mat[row]
                for (int t=0;t<words;++t) mat[r][t] ^= mat[row][t];
            }
        }
        ++row;
    }
    int rank = row;
    if (rank == n) {
        // nullspace dimension 0 => irreducible
        out.push_back(f);
        return;
    }
    // build basis vectors for nullspace: free columns -> basis vector with that free col set to 1
    vector<int> pivot_of_col(n, -1);
    for (int r=0;r<rank;++r) pivot_of_col[pivot_col[r]] = r;
    vector<int> free_cols;
    for (int c=0;c<n;++c) if (pivot_of_col[c] == -1) free_cols.push_back(c);
    int t = (int)free_cols.size();
    // Build basis as Poly (degree < n)
    vector<Poly> basis;
    for (int idx=0; idx < t; ++idx) {
        int fc = free_cols[idx];
        Poly v((n+63)>>6);
        // v[fc] = 1
        v.set_bit(fc);
        // for each pivot row r, pivot column pc, v[pc] = mat[r][fc]
        for (int r=0;r<rank;++r) {
            int pc = pivot_col[r];
            int wi = fc>>6; int bi = fc&63;
            if ( (mat[r][wi]>>bi) & 1ULL ) v.set_bit(pc);
        }
        v.trim();
        basis.push_back(v);
    }
    // If no basis (shouldn't happen), irreducible
    if (basis.empty()) { out.push_back(f); return; }

    // Enumerate non-trivial linear combinations of basis vectors to try to split f
    // If t is large, we limit enumeration but t typically small in practice
    int LIMIT_MASKS = (t <= 22) ? (1<<t) : (1<<22);
    for (int mask = 1; mask < (1<<t) && mask < LIMIT_MASKS; ++mask) {
        Poly h((n+63)>>6);
        for (int i=0;i<t;++i) if (mask & (1<<i)) h.xor_with(basis[i]);
        if (h.is_zero() || (h.deg() == 0 && h.get_bit(0))) continue;
        Poly d = gcd_poly(f, h);
        if (!d.is_zero() && d.deg() < f.deg() && !(d.deg()==0 && d.get_bit(0)==1)) {
            Poly q = divmod_poly(f, d).first;
            berlekamp_factor_rec(d, out);
            berlekamp_factor_rec(q, out);
            return;
        }
        // try h ^ 1
        Poly h1 = h; if (h1.get_bit(0)) { // toggle bit0
            int wi = 0; h1.ensure(1);
            h1.w[0] ^= 1ull;
        } else { h1.set_bit(0); }
        d = gcd_poly(f, h1);
        if (!d.is_zero() && d.deg() < f.deg()) {
            Poly q = divmod_poly(f, d).first;
            berlekamp_factor_rec(d, out);
            berlekamp_factor_rec(q, out);
            return;
        }
    }
    // if no split found, treat as irreducible
    out.push_back(f);
}

// Utility: convert Poly (lower S bits) to hex words (32-bit words little-endian)
vector<uint32_t> poly_to_words_le32(const Poly &p, int bits) {
    int words32 = (bits + 31) / 32;
    vector<uint32_t> out(words32, 0);
    for (int i=0;i<bits;++i) if (p.get_bit(i)) {
        int wi = i >> 5;
        int bi = i & 31;
        out[wi] |= (1u << bi);
    }
    return out;
}

// poly equality canonical string for map
string poly_key(const Poly &p) {
    string s;
    int d = p.deg();
    if (d < 0) return string("0");
    s.reserve(d+1);
    for (int i=0;i<=d;++i) s.push_back(p.get_bit(i) ? '1' : '0');
    return s;
}

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int S;
    if (!(cin >> S)) return 0;
    int N1 = S / 16; // number of input hex words provided
    vector<uint32_t> bwords(N1, 0);
    for (int i=0;i<N1;++i) {
        string h; cin >> h;
        uint32_t v=0;
        std::stringstream ss;
        ss << std::hex << h;
        ss >> v;
        bwords[i] = v;
    }
    // build polynomial f from bwords; bit k corresponds to coefficient x^k
    int maxBits = 2*S; // f degree <= 2S-2
    int w64 = (maxBits + 63) >> 6;
    Poly f(w64);
    for (int wi=0; wi < N1; ++wi) {
        uint32_t val = bwords[wi];
        for (int bit=0; bit<32; ++bit) if (val & (1u << bit)) {
            int pos = wi*32 + bit;
            f.set_bit(pos);
        }
    }
    f.trim();
    if (f.is_zero()) {
        // degenerate: output single zero solution (A=0,B=0)
        int wordsPerHalf = S / 32;
        bool firstOut = true;
        // print A words then B words (both zeros)
        for (int i=0;i<wordsPerHalf*2;++i) {
            if (!firstOut) cout << ' ';
            cout << "00000000";
            firstOut = false;
        }
        cout << '\n';
        return 0;
    }
    // Factor f
    vector<Poly> factors;
    berlekamp_factor(f, factors);
    // group identical factors and count multiplicity
    map<string, pair<Poly,int>> fmap;
    for (auto &p : factors) {
        string k = poly_key(p);
        if (fmap.count(k)==0) fmap[k] = {p, 1};
        else fmap[k].second++;
    }
    vector<pair<Poly,int>> facs;
    for (auto &kv : fmap) facs.push_back(kv.second);

    // generate divisors by recursive multiplication of factor powers
    vector<Poly> divisors;
    function<void(int, Poly)> gen = [&](int idx, Poly cur) {
        if (idx == (int)facs.size()) { divisors.push_back(cur); return; }
        Poly base = facs[idx].first;
        int exp = facs[idx].second;
        // k=0
        gen(idx+1, cur);
        Poly curpow = base;
        for (int e=1;e<=exp;++e) {
            cur = mul_full(cur, curpow);
            gen(idx+1, cur);
            curpow = mul_full(curpow, base);
        }
    };
    Poly one(1); one.set_bit(0);
    gen(0, one);

    int bitsPerHalf = S;
    int wordsPerHalf = S / 32;
    set<string> outputs;
    for (auto &d : divisors) {
        // other = f / d
        auto qr = divmod_poly(f, d);
        Poly other = qr.first; // quotient
        // validate degrees fit in half
        if (d.deg() <= bitsPerHalf-1 && other.deg() <= bitsPerHalf-1) {
            auto aw = poly_to_words_le32(d, bitsPerHalf);
            auto bw = poly_to_words_le32(other, bitsPerHalf);
            // format hex: each 32-bit word as 8-char hex, lowercase, little-endian sequence per half
            stringstream ss;
            ss << hex << nouppercase << setfill('0');
            for (int i=0;i<wordsPerHalf;++i) {
                ss << setw(8) << (uint32_t)aw[i];
                if (i+1<wordsPerHalf) ss << ' ';
            }
            ss << ' ';
            for (int i=0;i<wordsPerHalf;++i) {
                ss << setw(8) << (uint32_t)bw[i];
                if (i+1<wordsPerHalf) ss << ' ';
            }
            string s = ss.str();
            while (!s.empty() && s.back()==' ') s.pop_back();
            outputs.insert(s);
        }
    }
    for (auto &line : outputs) cout << line << '\n';
    return 0;
}
