#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiAggregateElement Basic(DataTypeKind kind, uint32_t width = 0) {
  DpiAggregateElement element;
  element.kind = kind;
  element.width = width;
  return element;
}

DpiAggregateElement Struct(std::vector<DpiAggregateElement> members) {
  DpiAggregateElement element;
  element.kind = DataTypeKind::kStruct;
  element.members = std::move(members);
  return element;
}

TEST(DpiUnpackedAggregates, AnAggregateOfLegalElementsIsAnArgument) {
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kBit, 8), Basic(DataTypeKind::kLogic, 32)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kChandle)})})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kByte), Basic(DataTypeKind::kBit, 16)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kEvent)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Struct({Basic(DataTypeKind::kEvent)})})));
}

TEST(DpiUnpackedAggregates, PurelyUnpackedElementsHaveTheCCompilersLayout) {
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal),
              Basic(DataTypeKind::kBit, 1), Basic(DataTypeKind::kChandle)})));
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kLongint)})})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kBit, 8)})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kInteger)})})));
}

struct Pair {
  int x;
  int y;
};

struct Record {
  int n;
  const char* name;
};

struct Triple {
  int a;
  uint32_t b[4][2];
  int c;
};

int PairSum(const Pair* p) { return (p->x * 10) + p->y; }

void PairMake(Pair* p) {
  p->x = 6;
  p->y = 9;
}

int RecordLength(const Record* r) {
  return (r->n * 100) + static_cast<int>(std::strlen(r->name));
}

int TripleOf(const Triple* t) {
  return (t->a * 10000) + static_cast<int>((t->b[2][0] & 0xFFU) * 10) + t->c;
}

void RunUnpackedStructDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  typedef struct { int x; int y; } pair;\n"
      "  typedef struct { int n; string name; } rec;\n"
      "  typedef struct { int a; bit [6:1][1:8] b [3:0]; int c; } triple;\n"
      "  import \"DPI-C\" function int pair_sum(input pair p);\n"
      "  import \"DPI-C\" function void pair_make(output pair p);\n"
      "  import \"DPI-C\" function int rec_len(input rec r);\n"
      "  import \"DPI-C\" function int tri3(input triple t);\n"
      "  pair a, b;\n"
      "  rec r;\n"
      "  triple tr;\n"
      "  int s, bx, by, rl, t3;\n"
      "  initial begin\n"
      "    a.x = 3; a.y = 4;\n"
      "    s = pair_sum(a);\n"
      "    pair_make(b);\n"
      "    bx = b.x; by = b.y;\n"
      "    r.n = 3; r.name = \"abcdef\";\n"
      "    rl = rec_len(r);\n"
      "    tr.a = 3; tr.c = 9; tr.b[2] = 48'h0000000000FF;\n"
      "    t3 = tri3(tr);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"pair_sum", reinterpret_cast<void*>(&PairSum)},
       {"pair_make", reinterpret_cast<void*>(&PairMake)},
       {"rec_len", reinterpret_cast<void*>(&RecordLength)},
       {"tri3", reinterpret_cast<void*>(&TripleOf)}},
      "annex_h_07_08_unpacked_structs");
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiUnpackedAggregates, AnUnpackedStructCrossesInTheCLayout) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "s"), 34U);
}

TEST(DpiUnpackedAggregates, AnUnpackedStructOutputIsCopiedBack) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "bx"), 6U);
  EXPECT_EQ(VariableValue(f, "by"), 9U);
}

TEST(DpiUnpackedAggregates, AStringMemberIsACString) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "rl"), 306U);
}

TEST(DpiUnpackedAggregates, AnArrayMemberOfPackedElementsIsCanonical) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "t3"), 32559U);
}

int PairsSum(const Pair* p) {
  int sum = 0;
  for (int i = 0; i < 4; ++i) sum = (sum * 100) + (p[i].x * 10) + p[i].y;
  return sum;
}

void PairsMake(Pair* q) {
  q[0] = {5, 6};
  q[1] = {7, 8};
}

void RunArrayOfStructsDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  typedef struct { int x; int y; } pair;\n"
      "  import \"DPI-C\" function int pairs_sum(input pair p [3:0]);\n"
      "  import \"DPI-C\" function void pairs_make(output pair q [1:0]);\n"
      "  pair ps [3:0];\n"
      "  pair qs [1:0];\n"
      "  int s, q0, q1;\n"
      "  initial begin\n"
      "    foreach (ps[k]) begin\n"
      "      ps[k].x = k + 1; ps[k].y = 9 - k;\n"
      "    end\n"
      "    s = pairs_sum(ps);\n"
      "    pairs_make(qs);\n"
      "    q0 = qs[0].x * 10 + qs[0].y;\n"
      "    q1 = qs[1].x * 10 + qs[1].y;\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"pairs_sum", reinterpret_cast<void*>(&PairsSum)},
       {"pairs_make", reinterpret_cast<void*>(&PairsMake)}},
      "annex_h_07_08_struct_arrays");
}

TEST(DpiUnpackedAggregates, ASizedArrayOfStructsCrossesAsACArray) {
  SimFixture f;
  RunArrayOfStructsDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "s"), 19283746U);
}

TEST(DpiUnpackedAggregates, ASizedOutputArrayOfStructsIsCopiedBack) {
  SimFixture f;
  RunArrayOfStructsDesign(f);
  EXPECT_EQ(VariableValue(f, "q0"), 56U);
  EXPECT_EQ(VariableValue(f, "q1"), 78U);
}

struct Inner {
  short s;
  double r;
};

struct Outer {
  char tag;
  Inner in;
  int last;
};

struct Mix {
  char a;
  double r;
  short s;
  void* h;
  int i;
};

struct Arrays {
  int a[3];
  int c;
};

struct RealArrays {
  short a;
  double r[2];
  int c;
};

struct Scattered {
  char a;
  short s;
  char b;
  long long l;
  int i;
};

int& AggregateCell() {
  static int cell = 77;
  return cell;
}

void* AggregateHandle() { return &AggregateCell(); }

void SeeOuter(const Outer* o) {
  SeeInC({o->tag, o->in.s, static_cast<long long>(o->in.r * 100), o->last});
}

void GiveOuter(Outer* o) { *o = Outer{5, Inner{-300, 2.5}, 70000}; }

void SeeMix(const Mix* m) {
  SeeInC({m->a, static_cast<long long>(m->r * 100), m->s,
          m->h == AggregateHandle() ? 1 : 0, m->i});
}

void SeeArrays(const Arrays* v) { SeeInC({v->a[0], v->a[1], v->a[2], v->c}); }

void SeeRealArrays(const RealArrays* v) {
  SeeInC({v->a, static_cast<long long>(v->r[0] * 100),
          static_cast<long long>(v->r[1] * 100), v->c});
}

void SeeScattered(const Scattered* v) {
  SeeInC({v->a, v->s, v->b, v->l, v->i});
}

void CallWithOuter() {
  auto take = NamedExport<void (*)(const Outer*)>("sv_take_outer");
  const Outer kOuter = {5, Inner{-300, 2.5}, 70000};
  if (take != nullptr) take(&kOuter);
}

void RunNested(const std::string& items, SimFixture& f) {
  RunModuleWithC(
      "  typedef struct { shortint s; real r; } inner;\n"
      "  typedef struct { byte tag; inner in; int last; } outer;\n"
      "  typedef struct { byte a; real r; shortint s; chandle h; int i; } "
      "mix;\n"
      "  typedef struct { int a [3]; int c; } arrays;\n"
      "  typedef struct { shortint a; real r [2]; int c; } real_arrays;\n"
      "  typedef struct { byte a; shortint s; byte b; longint l; int i; } "
      "scattered;\n" +
          items,
      f,
      {{"handle", CAddress(&AggregateHandle)},
       {"see_outer", CAddress(&SeeOuter)},
       {"give_outer", CAddress(&GiveOuter)},
       {"see_mix", CAddress(&SeeMix)},
       {"see_arrays", CAddress(&SeeArrays)},
       {"see_real_arrays", CAddress(&SeeRealArrays)},
       {"see_scattered", CAddress(&SeeScattered)},
       {"call_export", CAddress(&CallWithOuter)}},
      "annex_h_07_08_nested");
}

TEST(DpiNestedAggregates, DISABLED_AnInnerStructLiesWhereTheCCompilerPutsIt) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function void see_outer(input outer o);\n"
      "  outer o;\n"
      "  initial begin\n"
      "    o.tag = 5; o.in.s = -300; o.in.r = 2.5; o.last = 70000;\n"
      "    see_outer(o);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{5, -300, 250, 70000}));
}

TEST(DpiNestedAggregates, AnOutputsInnerStructIsCopiedBack) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function void give_outer(output outer o);\n"
      "  outer o;\n"
      "  bit tag, s, r, last;\n"
      "  initial begin\n"
      "    give_outer(o);\n"
      "    tag = o.tag == 5; s = o.in.s == -300; r = o.in.r == 2.5;\n"
      "    last = o.last == 70000;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "tag"), 1U);
  EXPECT_EQ(DesignValue(f, "s"), 1U);
  EXPECT_EQ(DesignValue(f, "r"), 1U);
  EXPECT_EQ(DesignValue(f, "last"), 1U);
}

TEST(DpiNestedAggregates, AnExportTakesANestedStruct) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" context function void call_export();\n"
      "  export \"DPI-C\" function sv_take_outer;\n"
      "  bit tag, s, r, last;\n"
      "  function void sv_take_outer(input outer o);\n"
      "    tag = o.tag == 5; s = o.in.s == -300; r = o.in.r == 2.5;\n"
      "    last = o.last == 70000;\n"
      "  endfunction\n"
      "  initial call_export();\n",
      f);
  EXPECT_EQ(DesignValue(f, "tag"), 1U);
  EXPECT_EQ(DesignValue(f, "s"), 1U);
  EXPECT_EQ(DesignValue(f, "r"), 1U);
  EXPECT_EQ(DesignValue(f, "last"), 1U);
}

TEST(DpiNestedAggregates, DISABLED_MembersArePaddedAsTheCCompilerPadsThem) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function chandle handle();\n"
      "  import \"DPI-C\" function void see_mix(input mix m);\n"
      "  mix m;\n"
      "  initial begin\n"
      "    m.a = 9; m.r = -1.25; m.s = -7; m.h = handle(); m.i = 12;\n"
      "    see_mix(m);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{9, -125, -7, 1, 12}));
}

TEST(DpiNestedAggregates, AMembersIntArrayHasTheCLayout) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function void see_arrays(input arrays v);\n"
      "  arrays v;\n"
      "  initial begin\n"
      "    v.a[0] = 1; v.a[1] = 2; v.a[2] = 3; v.c = 9;\n"
      "    see_arrays(v);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 2, 3, 9}));
}

TEST(DpiNestedAggregates, DISABLED_AMembersRealArrayHasTheCLayout) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function void see_real_arrays(input real_arrays v);\n"
      "  real_arrays v;\n"
      "  initial begin\n"
      "    v.a = -3; v.r[0] = 1.5; v.r[1] = -2.25; v.c = 9;\n"
      "    see_real_arrays(v);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{-3, 150, -225, 9}));
}

TEST(DpiNestedAggregates, IntegerMembersArePaddedAsTheCCompilerPadsThem) {
  SimFixture f;
  RunNested(
      "  import \"DPI-C\" function void see_scattered(input scattered v);\n"
      "  scattered v;\n"
      "  initial begin\n"
      "    v.a = 9; v.s = -300; v.b = -4; v.l = -64'sd5000000000; v.i = 12;\n"
      "    see_scattered(v);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{9, -300, -4, -5000000000LL, 12}));
}

}  // namespace
