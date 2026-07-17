#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NetDeclAssignSim, ScalarNetDeclAssignDrivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(NetDeclAssignSim, VectorNetDeclAssignDrivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] data = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NetDeclAssignSim, NetDeclAssignReEvaluatesOnChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] dst = src;\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #1;\n"
      "    src = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 42u);
}

// §10.3.1: the right-hand side of a net declaration assignment is a general
// expression, so a parameter is an admitted operand. Built from real source
// (a `parameter` declaration referenced by the net's initializer) and run
// end-to-end, the continuous assignment drives the resolved parameter value
// onto the net -- a different operand-resolution path than an inline literal.
TEST(NetDeclAssignSim, NetDeclAssignDrivesParameterValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 8'hAB;\n"
      "  wire [7:0] w = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §10.3.1: a localparam is likewise an admitted right-hand-side operand of a
// net declaration assignment. Declared with the `localparam` keyword and driven
// through the full pipeline, the net receives its value, confirming the
// continuous assignment resolves the named constant.
TEST(NetDeclAssignSim, NetDeclAssignDrivesLocalparamValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam Q = 8'h3C;\n"
      "  wire [7:0] w = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

}  // namespace
