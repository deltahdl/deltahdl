#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/variable.h"

using namespace delta;

SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, ProcessKindEnum) {
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

TEST(SimClause09_02, AllProcedureTypesCoexist) {
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

TEST(SimClause09_02, MultipleInitialsAllExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd1;\n"
      "  initial b = 8'd2;\n"
      "  initial c = 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
  EXPECT_EQ(vc->value.ToUint64(), 3u);
}

}
