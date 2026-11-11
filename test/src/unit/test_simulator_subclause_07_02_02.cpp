#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StructAssignmentSimulation, DefaultMemberValues_Applied) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a = 42; int b; } s_t;\n"
      "  s_t s;\n"
      "  int ra;\n"
      "  initial begin\n"
      "    ra = s.a;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 42u);
}

TEST(StructAssignmentSimulation, PartialDefaults_UnsetMembersZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a = 42; int b; } s_t;\n"
      "  s_t s;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    rb = s.b;\n"
      "  end\n"
      "endmodule\n",
      "rb");
  EXPECT_EQ(v, 0u);
}

TEST(StructAssignmentSimulation, ExplicitInit_SuppressesDefaults) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a = 42; int b = 99; } s_t;\n"
      "  s_t s = '{1, 2};\n"
      "  int ra;\n"
      "  initial begin\n"
      "    ra = s.a;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 1u);
}

TEST(StructAssignmentSimulation, WholeStructAssignment_CopiesAllMembers) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  s_t x, y;\n"
      "  int ra;\n"
      "  initial begin\n"
      "    x = '{10, 20};\n"
      "    y = x;\n"
      "    ra = y.a;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 10u);
}

TEST(StructAssignmentSimulation, WholeStructAssignment_SecondMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  s_t x, y;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    x = '{10, 20};\n"
      "    y = x;\n"
      "    rb = y.b;\n"
      "  end\n"
      "endmodule\n",
      "rb");
  EXPECT_EQ(v, 20u);
}

TEST(StructAssignmentSimulation, StructPassedToTaskAsWhole_InputArg) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  s_t src;\n"
      "  int result;\n"
      "  task get_b(input s_t arg, output int o);\n"
      "    o = arg.b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    src = '{10, 42};\n"
      "    get_b(src, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(StructAssignmentSimulation, StructReturnedFromTaskAsWhole_OutputArg) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  s_t dst;\n"
      "  int result;\n"
      "  task make(output s_t o);\n"
      "    o = '{7, 99};\n"
      "  endtask\n"
      "  initial begin\n"
      "    make(dst);\n"
      "    result = dst.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(StructAssignmentSimulation, MultipleDefaults_AllApplied) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a = 10; int b = 20; int c = 30; } s_t;\n"
      "  s_t s;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    ra = s.a;\n"
      "    rb = s.b;\n"
      "    rc = s.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 10}, {"rb", 20}, {"rc", 30}});
}

TEST(StructDefaultSim, MemberDefaultsReachEveryKindOfVariable) {
  const char* src =
      "package p;\n"
      "  typedef struct { int a = 7; int b = 11; } d_t;\n"
      "  d_t pv;\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  class C;\n"
      "    d_t s;\n"
      "    function int loc(); d_t l; return l.a * 100 + l.b; endfunction\n"
      "    function int prop(); return s.a * 100 + s.b; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int lo, pr, bl, pk, im;\n"
      "  initial begin\n"
      "    d_t b;\n"
      "    h = new;\n"
      "    lo = h.loc();\n"
      "    pr = h.prop();\n"
      "    bl = b.a * 100 + b.b;\n"
      "    pk = p::pv.a * 100 + p::pv.b;\n"
      "    im = pv.a * 100 + pv.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "lo"), 711u);
  EXPECT_EQ(RunAndGet(src, "pr"), 711u);
  EXPECT_EQ(RunAndGet(src, "bl"), 711u);
  EXPECT_EQ(RunAndGet(src, "pk"), 711u);
  EXPECT_EQ(RunAndGet(src, "im"), 711u);
}

TEST(StructAssignmentSimulation,
     StructPassedToAndFromFunctionsAndMethodsAsWhole) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct { int a; int b[2]; } s_t;\n"
          "  function s_t mk(input s_t x); mk = x; mk.a = x.a + 1; "
          "endfunction\n"
          "  function automatic void inc(inout s_t x); x.a++; endfunction\n"
          "  function automatic void dbl(ref s_t x); x.b[1] *= 2; endfunction\n"
          "  class C; function s_t pass(s_t x); return x; endfunction "
          "endclass\n"
          "  s_t s, r;\n"
          "  C h;\n"
          "  initial begin\n"
          "    s = '{1, '{2, 3}};\n"
          "    r = mk(s);\n"
          "    inc(r);\n"
          "    dbl(r);\n"
          "    h = new;\n"
          "    r = h.pass(r);\n"
          "    $display(\"%0d %0d %0d %0d\", r.a, r.b[0], r.b[1], s.a);\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 2 6 1\n");
}

TEST(StructAssignmentSimulation, ClauseExampleDefaultsAndTheirSuppression) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int constant = 4;\n"
                       "  typedef struct {\n"
                       "    int addr = 1 + constant;\n"
                       "    int crc;\n"
                       "    byte data [4] = '{4{1}};\n"
                       "  } packet1;\n"
                       "  packet1 p1;\n"
                       "  packet1 pi = '{1, 2, '{2, 3, 4, 5}};\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d "
                       "%0d\", p1.addr, p1.crc,\n"
                       "                   p1.data[0], p1.data[3], pi.addr, "
                       "pi.crc, pi.data[0],\n"
                       "                   pi.data[3]);\n"
                       "endmodule\n",
                       f),
            "5 0 1 1 1 2 2 5\n");
}

TEST(StructAssignmentSimulation,
     ExplicitInitializerIgnoresDefaultsInEveryKindOfVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct { int a = 5; int b = 6; } d_t;\n"
                       "  class C; d_t p = '{1, 2}; d_t q; endclass\n"
                       "  C h;\n"
                       "  d_t g;\n"
                       "  initial begin\n"
                       "    automatic d_t l = '{3, 4};\n"
                       "    automatic d_t m = l;\n"
                       "    h = new;\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", "
                       "h.p.a, h.p.b, l.a, l.b, m.a,\n"
                       "             m.b, h.q.a, g.b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 2 3 4 3 4 5 6\n");
}

TEST(StructAssignmentSimulation, NetWithoutNettypeIgnoresMemberDefaults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct { logic [7:0] a = 8'hFF; logic [7:0] b; } t_t;\n"
          "  wire t_t w;\n"
          "  wire t_t d;\n"
          "  t_t v;\n"
          "  assign d = '{8'h01, 8'h02};\n"
          "  initial begin\n"
          "    $display(\"%h %h\", w.a, w.b);\n"
          "    #1 $display(\"%h %h %h %h %h %h\", w.a, w.b, d.a, d.b, v.a, "
          "v.b);\n"
          "  end\n"
          "endmodule\n",
          f),
      "zz zz\nzz zz 01 02 ff xx\n");
}

TEST(StructAssignmentSimulation,
     DISABLED_NetOfAUserDefinedNettypeKeepsMemberDefaults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct { logic [7:0] a = 8'hFF; logic [7:0] b; } t_t;\n"
          "  nettype t_t nt;\n"
          "  nt n;\n"
          "  initial #1 $display(\"%h %h\", n.a, n.b);\n"
          "endmodule\n",
          f),
      "ff xx\n");
}

}  // namespace
