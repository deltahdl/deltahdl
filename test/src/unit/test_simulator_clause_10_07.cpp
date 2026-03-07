#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.7: Truncation — RHS wider than LHS, MSBs discarded.
TEST(SimCh10e, TruncationDiscardsMSBs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] a;\n"
      "  initial begin\n"
      "    a = 8'hff;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // 8'hff = 8'b1111_1111, truncated to 6 bits = 6'b11_1111 = 6'h3f.
  EXPECT_EQ(a->value.ToUint64(), 0x3Fu);
}

// §10.7: Truncation of signed value into narrower signed (Example 1).
TEST(SimCh10e, TruncationSignedIntoNarrowerSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [4:0] b;\n"
      "  initial begin\n"
      "    b = 8'hff;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  // 8'hff = 8'b1111_1111, truncated to 5 bits = 5'b1_1111 = 5'h1f.
  EXPECT_EQ(b->value.ToUint64(), 0x1Fu);
}

// §10.7: Extension — RHS narrower than LHS, zero-padded (unsigned).
TEST(SimCh10e, ExtensionZeroPadUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* wide = f.ctx.FindVariable("wide");
  ASSERT_NE(wide, nullptr);
  // 8'hAB zero-padded to 16 bits = 16'h00AB.
  EXPECT_EQ(wide->value.ToUint64(), 0x00ABu);
  EXPECT_EQ(wide->value.width, 16u);
}

// §10.7: Truncation to 4-bit.
TEST(SimCh10e, TruncationTo4Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin\n"
      "    narrow = 32'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  // 32'hABCD truncated to 4 bits = 4'hD.
  EXPECT_EQ(var->value.ToUint64(), 0xDu);
}

// §10.7: NBA truncation.
TEST(SimCh10e, NBATruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] narrow;\n"
      "  initial begin\n"
      "    narrow <= 32'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// §10.7: NBA extension.
TEST(SimCh10e, NBAExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "  initial begin\n"
      "    wide <= 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
  EXPECT_EQ(var->value.width, 32u);
}

// §10.7: Continuous assignment truncation.
TEST(SimCh10e, ContAssignTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] out;\n"
      "  logic [7:0] in_val = 8'hAB;\n"
      "  assign out = in_val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// §10.7: Continuous assignment extension.
TEST(SimCh10e, ContAssignExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] out;\n"
      "  logic [3:0] in_val = 4'hA;\n"
      "  assign out = in_val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x000Au);
}

// §10.7: Same-width assignment (no truncation or extension).
TEST(SimCh10e, SameWidthNoChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xCAu);
}

}  // namespace
