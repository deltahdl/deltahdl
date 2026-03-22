#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(TaggedUnionSimulation, ChangeTag) {
  SimFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

// §7.3.2: Tagged assignment sets tag and value; read back via matching member.
TEST(TaggedUnionSimulation, TaggedAssignment_SetsTagAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Valid 42;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.3.2: Reassigning with different tag updates the active member.
TEST(TaggedUnionSimulation, TaggedAssignment_OverwriteTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 10;\n"
      "    u = tagged B 20;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// §7.3.2: Void member tagged assignment (tag only, no value).
TEST(TaggedUnionSimulation, VoidMemberTaggedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Invalid;\n"
      "    u = tagged Valid 99;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

}  // namespace
