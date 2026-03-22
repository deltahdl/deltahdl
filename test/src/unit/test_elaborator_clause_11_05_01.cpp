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

TEST(PrimaryElaboration, PrimaryPartSelectRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[15:8];\n"
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

TEST(AlwaysLatchBasicSim, BitSelectHighBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'b1010_0101;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[7];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);

  EXPECT_EQ(q->value.ToUint64(), 1u);
}

TEST(AlwaysLatchBasicSim, PartSelectLowerNibble) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'hAB;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);

  EXPECT_EQ(q->value.ToUint64(), 0xBu);
}

TEST(AlwaysLatchBasicSim, PartSelectUpperNibble) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'hAB;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);

  EXPECT_EQ(q->value.ToUint64(), 0xAu);
}

TEST(BlockingAssignSim, BlockingAssignSplitPacked) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] packed_val;\n"
      "  logic [7:0] hi, lo;\n"
      "  initial begin\n"
      "    packed_val = 16'hDEAD;\n"
      "    hi = packed_val[15:8];\n"
      "    lo = packed_val[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0xDEu);
  EXPECT_EQ(lo->value.ToUint64(), 0xADu);
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
