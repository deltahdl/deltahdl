#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(UnionSimulation, UnpackedUnionMemberWriteReadBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int i; int j; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.i = 42;\n"
      "    result = u.i;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(UnionSimulation, UnpackedUnionSingleStorage_CrossMemberRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int a; int b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 99;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(UnionSimulation, UnpackedUnionDefaultInit_IntFirstMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { int i; logic [31:0] l; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = u.i;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(UnionSimulation, UnpackedUnionDefaultInit_FourStateFirstMemberIsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union { logic [7:0] a; int b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $isunknown(u.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(UnionSimulation, UnpackedUnionCommonInitialSequenceSharedPrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int tag; int x; } sa_t;\n"
      "  typedef struct { int tag; int y; } sb_t;\n"
      "  typedef union { sa_t a; sb_t b; } u_t;\n"
      "  u_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a.tag = 42;\n"
      "    result = u.b.tag;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(UnionShortrealMemberWrite, DISABLED_StaticUnionKeepsTheValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef union { shortreal r; int k; } u_t;\n"
                       "  u_t u;\n"
                       "  initial begin\n"
                       "    u.r = 3.5;\n"
                       "    $display(\"%0.2f\", u.r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3.50\n");
}

TEST(UnionShortrealMemberWrite, RealMemberOfAStaticUnionKeepsTheValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef union { real r; longint k; } u_t;\n"
                       "  u_t u;\n"
                       "  initial begin\n"
                       "    u.r = 3.5;\n"
                       "    $display(\"%0.2f\", u.r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3.50\n");
}

TEST(UnionDefaultValue, FirstMemberDefaultInDeclarativeScopes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef union {int i; logic [7:0] l;} ui_t;\n"
          "package pk; ui_t pv; endpackage\n"
          "interface I; union {logic [3:0] l; int k;} iu; endinterface\n"
          "program P;\n"
          "  union {logic [3:0] l; int k;} pu;\n"
          "  initial #1 $display(\"p %b\", pu.l);\n"
          "endprogram\n"
          "module t;\n"
          "  typedef enum bit [1:0] {A = 2, B = 1} e_t;\n"
          "  I ii(); P pp();\n"
          "  if (1) begin : g union {logic [3:0] l; int k;} gu; end\n"
          "  union {real r; longint k;} ur;\n"
          "  union {e_t e; int k;} ue;\n"
          "  union {union {logic [3:0] a; int b;} n; int k;} un;\n"
          "  union {logic [3:0] l; int k;} ua [2];\n"
          "  initial $display(\"%b %b %f %0d %b %b %0d\", ii.iu.l, g.gu.l, "
          "ur.r, ue.e, un.n.a, ua[1].l, pk::pv.i);\n"
          "endmodule\n",
          f),
      "xxxx xxxx 0.000000 0 xxxx xxxx 0\np xxxx\n");
}

TEST(UnionDefaultValue,
     DISABLED_FirstMemberDefaultInProceduralScopesAndClasses) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  class C; union {logic [3:0] l; int k;} cu; endclass\n"
          "  function automatic int fa();\n"
          "    union {logic [3:0] l; int k;} u; return $isunknown(u.l);\n"
          "  endfunction\n"
          "  function static int fs();\n"
          "    union {logic [3:0] l; int k;} u; return $isunknown(u.l);\n"
          "  endfunction\n"
          "  task automatic tk();\n"
          "    union {logic [3:0] l; int k;} u; $display(\"t %b\", u.l);\n"
          "  endtask\n"
          "  C c;\n"
          "  initial begin\n"
          "    union {logic [3:0] l; int k;} u;\n"
          "    c = new;\n"
          "    $display(\"%b %b %0d %0d\", u.l, c.cu.l, fa(), fs());\n"
          "    tk();\n"
          "  end\n"
          "endmodule\n",
          f),
      "xxxx xxxx 1 1\nt xxxx\n");
}

TEST(UnionDefaultValue,
     DISABLED_FirstMemberStructureGivesEachMemberItsDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {logic [3:0] a; int b; real r;} s_t;\n"
                       "  union {s_t s; int k;} us;\n"
                       "  initial $display(\"%b %0d %f\", us.s.a, us.s.b, "
                       "us.s.r);\n"
                       "endmodule\n",
                       f),
            "xxxx 0 0.000000\n");
}

TEST(UnionCommonInitialSequence, EquivalentPrefixReadsThroughEitherStructure) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct {int tag; int x;} sa_t;\n"
                 "  typedef struct {bit signed [31:0] tag; int y;} sb_t;\n"
                 "  typedef union {sa_t a; sb_t b;} u_t;\n"
                 "  class C; u_t u; endclass\n"
                 "  function automatic int f();\n"
                 "    u_t u; u.a.tag = 5; return u.b.tag;\n"
                 "  endfunction\n"
                 "  C c; u_t m;\n"
                 "  initial begin\n"
                 "    c = new; c.u.b.tag = 3; m.a.tag = -6;\n"
                 "    $display(\"%0d %0d %0d\", c.u.a.tag, f(), m.b.tag);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "3 5 -6\n");
}

TEST(UnionCommonInitialSequence,
     DISABLED_PrefixOfStructuresOfDifferentSizesReadsThroughEither) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct {int tag; bit [7:0] a; int x;} sa_t;\n"
          "  typedef struct {int tag; byte unsigned a; real y; int z;} sb_t;\n"
          "  typedef union {sa_t a; sb_t b;} u_t;\n"
          "  class C; u_t u; endclass\n"
          "  function automatic int f();\n"
          "    u_t u; u.a.tag = 5; u.a.a = 9; return u.b.tag + u.b.a;\n"
          "  endfunction\n"
          "  C c; u_t m;\n"
          "  initial begin\n"
          "    c = new; c.u.b.tag = 3; c.u.b.a = 4;\n"
          "    m.a.tag = -2; m.a.a = 8'hff;\n"
          "    $display(\"%0d %0d %0d %0d %0d\", c.u.a.tag, c.u.a.a, f(), "
          "m.b.tag, m.b.a);\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 4 14 -2 255\n");
}

TEST(UnionSimulation, ClauseExamplesWriteAndReadTheirMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union {int i; shortreal f;} num;\n"
                       "  num n;\n"
                       "  typedef struct {\n"
                       "    bit isfloat;\n"
                       "    union {int i; shortreal f;} n;\n"
                       "  } tagged_st;\n"
                       "  tagged_st ts;\n"
                       "  initial begin\n"
                       "    n.i = 5; n.f = 0.0;\n"
                       "    $display(\"%0d\", n.i);\n"
                       "    ts.isfloat = 1; ts.n.i = 7;\n"
                       "    $display(\"%0d %0d\", ts.isfloat, ts.n.i);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n1 7\n");
}

}  // namespace
