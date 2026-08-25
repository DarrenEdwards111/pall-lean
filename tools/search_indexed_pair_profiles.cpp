// Exhaustive audit for the three-gate/four-variable indexed pair-profile frontier.
// Compile with: c++ -O3 -std=c++20 tools/search_indexed_pair_profiles.cpp -o /tmp/search-indexed
#include <array>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

struct Clause { int a, b; }; // literals: 2*variable + sign (0 positive, 1 negative)
struct Gate { int x, y; uint8_t support, local, good; };

static std::vector<Clause> clauses;
static std::vector<Gate> gates;

static int type(const Clause& x, const Clause& y) {
  int same = 0, opposite = 0, support = 0;
  bool seen[4] = {};
  for (int p : {x.a, x.b}) seen[p / 2] = true;
  for (int p : {y.a, y.b}) seen[p / 2] = true;
  for (bool z : seen) support += z;
  for (int p : {x.a, x.b}) for (int q : {y.a, y.b}) if (p / 2 == q / 2) {
    if ((p & 1) == (q & 1)) ++same; else ++opposite;
  }
  return (same * 3 + opposite) * 5 + support;
}

// Exact depth of the Lean canonicalDT recursion for a two-clause gate.
static int depth_rec(const Gate& g, std::array<int,4> rho, int fuel) {
  auto lit_value = [&](int lit) -> int {
    int v = rho[lit / 2];
    if (v < 0) return -1;
    return (lit & 1) ? 1 - v : v;
  };
  const Clause* active = nullptr;
  for (int ci : {g.x, g.y}) {
    const Clause& c = clauses[ci];
    int va = lit_value(c.a), vb = lit_value(c.b);
    if (va == 1 && vb == 1) return 0; // anyTermSat
  }
  if (fuel == 0) return 0;
  for (int ci : {g.x, g.y}) {
    const Clause& c = clauses[ci];
    int va = lit_value(c.a), vb = lit_value(c.b);
    if (va != 0 && vb != 0) { active = &c; break; }
  }
  if (!active) return 0;
  int lit = lit_value(active->a) < 0 ? active->a : active->b;
  int q = lit / 2;
  auto lo = rho, hi = rho; lo[q] = 0; hi[q] = 1;
  int dl = depth_rec(g, lo, fuel - 1), dh = depth_rec(g, hi, fuel - 1);
  return 1 + (dl > dh ? dl : dh);
}

static std::string key(const Gate& a, const Gate& b, const Gate& c) {
  // Each histogram contains four witnesses, so encode only its sorted four type indices.
  auto hist = [](const Gate& p, const Gate& q) {
    std::array<int,4> z = {type(clauses[p.x], clauses[q.x]), type(clauses[p.x], clauses[q.y]),
                           type(clauses[p.y], clauses[q.x]), type(clauses[p.y], clauses[q.y])};
    std::sort(z.begin(), z.end());
    std::string s;
    for (int v : z) s.push_back(char(v));
    return s;
  };
  std::string s;
  s.push_back(char(a.support | b.support | c.support));
  s.push_back(char(a.local)); s.push_back(char(b.local)); s.push_back(char(c.local));
  s += hist(a,b); s += hist(a,c); s += hist(b,c);
  return s;
}

static void print_gate(const Gate& g) {
  auto pc = [](const Clause& c) {
    auto pl = [](int x) { std::cout << ((x & 1) ? "-" : "+") << x/2; };
    pl(c.a); pl(c.b);
  };
  std::cout << "{"; pc(clauses[g.x]); std::cout << ","; pc(clauses[g.y]); std::cout << "}";
}

int main() {
  for (int i=0;i<4;++i) for (int j=i+1;j<4;++j)
    for (int si=0;si<2;++si) for (int sj=0;sj<2;++sj) clauses.push_back({2*i+si,2*j+sj});
  std::array<int,4> free = {-1,-1,-1,-1};
  for (int x=0;x<(int)clauses.size();++x) for (int y=x+1;y<(int)clauses.size();++y) {
    Gate g{x,y,0,(uint8_t)type(clauses[x],clauses[y]),0};
    for (int lit : {clauses[x].a,clauses[x].b,clauses[y].a,clauses[y].b}) g.support |= 1u << (lit/2);
    if (depth_rec(g, free, 4) <= 1) continue; // only active indexed gates
    for (int q=0;q<4;++q) {
      bool ok=true;
      for (int v=0;v<2;++v) { auto r=free; r[q]=v; ok &= depth_rec(g,r,4)<=1; }
      if (ok) g.good |= 1u << q;
    }
    gates.push_back(g);
  }
  struct Seen { int a=-1,b=-1,c=-1; bool one=false; };
  std::unordered_map<std::string,Seen> seen;
  uint64_t families=0;
  // Keep all indexed orders: two matched families may require different gate permutations.
  for (int i=0;i<(int)gates.size();++i) for (int j=0;j<(int)gates.size();++j)
    for (int k=0;k<(int)gates.size();++k) {
      ++families;
      bool one = (gates[i].good & gates[j].good & gates[k].good) != 0;
      std::string sig=key(gates[i],gates[j],gates[k]);
      auto [it,inserted]=seen.emplace(sig,Seen{i,j,k,one});
      if (!inserted && it->second.one != one) {
        std::cout << "MATCH families=" << families << " active_gates=" << gates.size() << "\n";
        print_gate(gates[it->second.a]); std::cout << " "; print_gate(gates[it->second.b]); std::cout << " "; print_gate(gates[it->second.c]);
        std::cout << " one=" << it->second.one << "\n";
        print_gate(gates[i]); std::cout << " "; print_gate(gates[j]); std::cout << " "; print_gate(gates[k]);
        std::cout << " one=" << one << "\n";
        return 0;
      }
    }
  std::cout << "NO_MATCH families=" << families << " active_gates=" << gates.size()
            << " signatures=" << seen.size() << "\n";
}
