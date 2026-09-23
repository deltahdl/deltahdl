#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StructuredProcedureSimulation, AllProcedureTypesCoexist) {
  SimFixture f;
  auto* sum = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb sum = a + b;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 30u);
}

// The $finish at 21 falls between the firings at 20 and 22: §4.7 leaves open
// the order of two processes due at one time, and §20.2 runs nothing of that
// step after the $finish, so it is kept off a firing's own tick.
TEST(StructuredProcedureSimulation, AlwaysRepeatsUntilTermination) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial count = 0;\n"
      "  always #2 count = count + 1;\n"
      "  initial #21 $finish;\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 10u);
}

TEST(StructuredProcedureSimulation, NoImpliedOrderInitialAndAlways) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  always #1 b = a;\n"
      "  initial #2 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 42u);
  EXPECT_EQ(vb->value.ToUint64(), 42u);
}

// Each always fires at 2, 4, 6, 8 and 10, and the $finish at 11 falls off
// those ticks, for the reason AlwaysRepeatsUntilTermination gives.
TEST(StructuredProcedureSimulation, NoLimitOnAlwaysCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b, c;\n"
      "  initial begin a = 0; b = 0; c = 0; end\n"
      "  always #2 a = a + 1;\n"
      "  always #2 b = b + 2;\n"
      "  always #2 c = c + 3;\n"
      "  initial #11 $finish;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 5u}, {"b", 10u}, {"c", 15u}});
}

TEST(StructuredProcedureSimulation, InitialAndAlwaysEnabledAtBeginning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial a = 1;\n"
      "  always begin b = 1; #1 $finish; end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}});
}

TEST(StructuredProcedureSimulation, InitialExecutesOnlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    #1;\n"
      "    count = count + 1;\n"
      "  end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 1u);
}

TEST(StructuredProcedureSimulation, FinalRunsAtEndOfSimulation) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] marker;\n"
      "  initial begin marker = 1; #5 $finish; end\n"
      "  final marker = 99;\n"
      "endmodule\n",
      "marker");
  EXPECT_EQ(val, 99u);
}

TEST(StructuredProcedureSimulation, FinalExecutesOnlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] marker;\n"
      "  initial begin marker = 0; #1 $finish; end\n"
      "  final marker = marker + 1;\n"
      "endmodule\n",
      "marker");
  EXPECT_EQ(val, 1u);
}

}  // namespace
