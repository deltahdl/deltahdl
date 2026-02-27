// §9.3.2: Parallel blocks


#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(Lowerer, ForkJoinNone) {
  // fork/join_none: parent continues immediately.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "    join_none\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(Lowerer, ForkJoin) {
  // fork/join: parent waits for all children to complete.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b, done;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 10;\n"
      "      begin #2 b = 20; end\n"
      "    join\n"
      "    done = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  struct {
    const char* name;
    uint64_t expected;
  } const kCases[] = {{"a", 10u}, {"b", 20u}, {"done", 1u}};
  for (const auto& c : kCases) {
    auto* var = f.ctx.FindVariable(c.name);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->value.ToUint64(), c.expected);
  }
}

// Sim test fixture
// ---------------------------------------------------------------------------
// Simulation: §9.3.2 parallel block fork/join semantics
// ---------------------------------------------------------------------------
// fork/join: all children execute
TEST(SimA603, ForkJoinAllChildrenExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd10;\n"
      "      b = 8'd20;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

// fork/join_none: all children execute, parent continues immediately
TEST(SimA603, ForkJoinNoneChildrenExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "    join_none\n"
      "    c = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

// fork/join_any: all children execute
TEST(SimA603, ForkJoinAnyChildrenExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd7;\n"
      "      b = 8'd8;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 7u);
  EXPECT_EQ(b->value.ToUint64(), 8u);
}

// fork with single begin-end: executes as single sequential process
TEST(SimA603, ForkWithSingleBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        x = 8'd1;\n"
      "        x = 8'd2;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// Empty fork-join completes immediately
TEST(SimA603, EmptyForkJoin) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    fork join\n"
      "    x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
