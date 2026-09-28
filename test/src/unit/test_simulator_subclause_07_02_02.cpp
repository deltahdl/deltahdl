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

// §7.2.2: a variable of a structure type with no initializer takes each
// member's default, wherever the variable is declared -- a class property, a
// method's local, a block's local and a package's variable, read through
// `pkg::` and a wildcard import -- so every one reads a = 7 and b = 11, as a
// module variable already did. Each read 0 0.
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

}  // namespace
