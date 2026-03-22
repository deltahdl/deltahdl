#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.2.2: Default member values applied when no explicit init.
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

// §7.2.2: Members without defaults get type-appropriate zero.
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

// §7.2.2: Explicit init suppresses typedef defaults.
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

// §7.2.2: Whole struct assignment copies all members.
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

// §7.2.2: Whole struct assignment copies second member too.
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

// §7.2.2: Multiple members with different default values.
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

}  // namespace
