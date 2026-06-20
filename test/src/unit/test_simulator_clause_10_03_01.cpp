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

}  // namespace
