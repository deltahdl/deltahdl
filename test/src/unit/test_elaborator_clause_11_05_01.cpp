#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ExpressionElaboration, IndexedPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[0+:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantRangePackedDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, PrimaryHierIdentSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, GenvarExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  logic [N-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
TEST(VarLvaluePartSelect, VarLvaluePartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(SelectElaboration, ScalarBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic y;\n"
      "  assign y = x[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, ScalarPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic [3:0] y;\n"
      "  assign y = x[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, IndexedPartSelectWidthMustBeConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  initial begin w = 8; y = data[0+:w]; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, IndexedPartSelectWidthMustBePositive) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0+:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealVariablePartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [3:0] y;\n"
      "  assign y = r[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, NonIndexedPartSelectBoundsMustBeConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[w:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, PartSelectReversedOrderError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0:7];\n"
      "endmodule\n",
      f);
  // data is declared descending [15:0], so the first index must be the larger
  // one; data[0:7] reverses that and is illegal.
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, PartSelectAscendingOrderOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [0:15] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0:7];\n"
      "endmodule\n",
      f);
  // For an ascending [0:15] declaration the lower index is the more
  // significant bit, so data[0:7] is a correctly ordered part-select.
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealParameterSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  logic y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}
