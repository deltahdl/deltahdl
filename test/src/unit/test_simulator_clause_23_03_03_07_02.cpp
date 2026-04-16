
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Interconnect on gate input propagates value as scalar wire ---

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateInputPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module driver(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  driver d(.a(ic));\n"
      "  and (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnBufGateInputPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module driver(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  driver d(.a(ic));\n"
      "  buf (y, ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnNotGateInputPropagatesInvertedValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module driver(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  driver d(.a(ic));\n"
      "  not (y, ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// --- Interconnect on gate output receives value as scalar wire ---

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateOutputReceivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  interconnect ic;\n"
      "  and (ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnPullupReceivesOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  pullup (ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnPulldownReceivesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  pulldown (ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
