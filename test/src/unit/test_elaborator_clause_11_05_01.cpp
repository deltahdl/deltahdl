// §11.5.1: Vector bit-select and part-select addressing

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § part_select_range — indexed part select elaborates
TEST(ElabA83, IndexedPartSelectElaborates) {
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

// § constant_range — packed dimension range elaborates
TEST(ElabA83, ConstantRangePackedDimElaborates) {
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

// § primary_literal — part select range elaborates
TEST(ElabA84, PrimaryPartSelectRangeElaborates) {
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

TEST(Elaboration, RealIndex_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// § primary — hierarchical identifier with select elaborates
TEST(ElabA84, PrimaryHierIdentSelectElaborates) {
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

// 15. Bit-select on a different bit position.
TEST(SimCh9c, BitSelectHighBit) {
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
  // d = 0xA5 = 0b10100101; d[7] = 1.
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

// =============================================================================
// §9.2.3: always_latch with part-select
// =============================================================================
// 16. Part-select extracting lower nibble.
TEST(SimCh9c, PartSelectLowerNibble) {
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
  // d = 0xAB; d[3:0] = 0xB.
  EXPECT_EQ(q->value.ToUint64(), 0xBu);
}

// 17. Part-select extracting upper nibble.
TEST(SimCh9c, PartSelectUpperNibble) {
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
  // d = 0xAB; d[7:4] = 0xA.
  EXPECT_EQ(q->value.ToUint64(), 0xAu);
}

}  // namespace
