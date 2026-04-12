#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StructuredProcedureSimulation, ProcessKindEnum) {
  struct {
    ProcessKind kind;
    uint8_t expected;
  } const kCases[] = {
      {ProcessKind::kInitial, 0},    {ProcessKind::kAlways, 1},
      {ProcessKind::kAlwaysComb, 2}, {ProcessKind::kAlwaysLatch, 3},
      {ProcessKind::kAlwaysFF, 4},   {ProcessKind::kFinal, 5},
      {ProcessKind::kContAssign, 6},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(static_cast<uint8_t>(c.kind), c.expected);
  }
}

TEST(StructuredProcedureSimulation, AllProcedureTypesCoexist) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb sum = a + b;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* sum = f.ctx.FindVariable("sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 30u);
}

TEST(StructuredProcedureSimulation, AlwaysRepeatsUntilTermination) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial count = 0;\n"
      "  always #1 count = count + 1;\n"
      "  initial #10 $finish;\n"
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

TEST(StructuredProcedureSimulation, NoLimitOnAlwaysCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b, c;\n"
      "  initial begin a = 0; b = 0; c = 0; end\n"
      "  always #1 a = a + 1;\n"
      "  always #1 b = b + 2;\n"
      "  always #1 c = c + 3;\n"
      "  initial #5 $finish;\n"
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 1u);
}

}  // namespace
