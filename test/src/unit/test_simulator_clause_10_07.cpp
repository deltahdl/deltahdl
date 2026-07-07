#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentExtensionTruncationSim, TruncationDiscardsMSBs) {
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

  EXPECT_EQ(a->value.ToUint64(), 0x3Fu);
}

TEST(AssignmentExtensionTruncationSim, TruncationSignedIntoNarrowerSigned) {
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

  EXPECT_EQ(b->value.ToUint64(), 0x1Fu);
}

TEST(AssignmentExtensionTruncationSim, ExtensionZeroPadUnsigned) {
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

  EXPECT_EQ(wide->value.ToUint64(), 0x00ABu);
  EXPECT_EQ(wide->value.width, 16u);
}

TEST(AssignmentExtensionTruncationSim, TruncationTo4Bit) {
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

  EXPECT_EQ(var->value.ToUint64(), 0xDu);
}

TEST(AssignmentExtensionTruncationSim, NBATruncation) {
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

TEST(AssignmentExtensionTruncationSim, NBAExtension) {
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

TEST(AssignmentExtensionTruncationSim, ContAssignTruncation) {
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

TEST(AssignmentExtensionTruncationSim, ContAssignExtension) {
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

TEST(AssignmentExtensionTruncationSim, RhsSizedToLhsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin narrow = 4'hF; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, SignedRhsSignExtendsToLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin narrow = -4'sd1; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(AssignmentExtensionTruncationSim, WideRhsTruncated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  initial begin wide = 8'hAB; narrow = wide; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(AssignmentExtensionTruncationSim, SignedRhsToUnsignedLhsSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic signed [3:0] src;\n"
      "  initial begin src = -4'sd2; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFEu);
}

TEST(AssignmentExtensionTruncationSim, UnsignedRhsToSignedLhsZeroExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] dst;\n"
      "  logic [3:0] src;\n"
      "  initial begin src = 4'hF; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, SignedPositiveRhsZeroFillsUpperBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] dst;\n"
      "  logic signed [3:0] src;\n"
      "  initial begin src = 4'sb0101; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x05u);
}

TEST(AssignmentExtensionTruncationSim, SameWidthNoExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic [7:0] src;\n"
      "  initial begin src = 8'hA5; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(AssignmentExtensionTruncationSim, SignedWideTruncated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] dst;\n"
      "  logic signed [7:0] src;\n"
      "  initial begin src = -8'sd3; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDu);
}

TEST(AssignmentExtensionTruncationSim,
     RhsExpressionSignednessDeterminesExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst_signed_rhs;\n"
      "  logic [7:0] dst_unsigned_rhs;\n"
      "  logic [3:0] val;\n"
      "  initial begin\n"
      "    val = 4'hF;\n"
      "    dst_signed_rhs = $signed(val);\n"
      "    dst_unsigned_rhs = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("dst_signed_rhs");
  auto* u = f.ctx.FindVariable("dst_unsigned_rhs");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 0xFFu);
  EXPECT_EQ(u->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, LhsContextWidensRhsExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [4:0] sum;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 4'h1;\n"
      "    sum = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x10u);
}

TEST(AssignmentExtensionTruncationSim, TruncationChangesSignOfResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] dst;\n"
      "  logic signed [7:0] src;\n"
      "  initial begin\n"
      "    src = 8'sd120;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8u);
}

TEST(AssignmentExtensionTruncationSim, TruncationToOneBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic dst;\n"
      "  initial dst = 8'hFE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AssignmentExtensionTruncationSim, ExtensionOneBitToWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic src;\n"
      "  initial begin src = 1'b1; dst = src; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x01u);
}

TEST(AssignmentExtensionTruncationSim, NBASignedExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin\n"
      "    narrow = -4'sd3;\n"
      "    wide <= narrow;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFDu);
}

TEST(AssignmentExtensionTruncationSim, ContAssignSignedExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow = -4'sd5;\n"
      "  assign wide = narrow;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFBu);
}

TEST(AssignmentExtensionTruncationSim, ContAssignSignedTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] narrow;\n"
      "  logic signed [7:0] wide = -8'sd113;\n"
      "  assign narrow = wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

TEST(AssignmentExtensionTruncationSim, SignedLiteralTruncatedToUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] a;\n"
      "  initial a = 8'sh8f;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// Truncation discards the high bits even when they are unknown (x): the
// surviving low bits are fully known and retain their value.
TEST(AssignmentExtensionTruncationSim, TruncationDiscardsUnknownMSBs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow = 8'bxxxx_0101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

// Sign-extension of a signed right-hand side replicates the sign bit even when
// that bit is unknown: the padded high bits become unknown too. Checked via the
// unknown-flag (bval) so the result is independent of the x/z encoding.
TEST(AssignmentExtensionTruncationSim, SignExtensionPropagatesUnknownSignBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin narrow = 4'bx101; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_FALSE(var->value.IsKnown());
  // The four padded bits [7:4] are all unknown, mirroring the unknown sign bit.
  EXPECT_EQ((var->value.words[0].bval >> 4) & 0xFull, 0xFull);
}

// Sign-extension spanning a 64-bit word boundary: a 68-bit signed value with
// its sign bit set widens to 72 bits, and the padded high bits are filled with
// ones (sign, not zero), exercising the multi-word fill path of the resize.
TEST(AssignmentExtensionTruncationSim, WideSignExtensionAcrossWordBoundary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [71:0] wide;\n"
      "  logic signed [67:0] narrow;\n"
      "  initial begin narrow = 68'hF_FFFF_FFFF_FFFF_FFFF; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 72u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, ~uint64_t{0});
  EXPECT_EQ(var->value.words[0].bval, 0u);
  // Top word holds bits [71:64]; sign-extension fills the low 8 with ones.
  EXPECT_EQ(var->value.words[1].aval & 0xFFull, 0xFFull);
  EXPECT_EQ(var->value.words[1].bval & 0xFFull, 0u);
}

// Truncation from a value wider than 64 bits discards the entire high word and
// keeps the low bits of the narrow target.
TEST(AssignmentExtensionTruncationSim, WideTruncationDiscardsHighWord) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [71:0] wide;\n"
      "  initial begin wide = 72'hFF000000000000000A; narrow = wide; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// A variable declaration initializer is a procedural assignment, so §10.7's
// width adjustment applies at that syntactic position too: an initializer wider
// than the declared target has its excess high bits discarded. Distinct from
// the blocking/nonblocking/continuous positions above because the initializer
// flows through the variable-lowering path rather than a statement-execution
// path.
TEST(AssignmentExtensionTruncationSim, DeclarationInitializerTruncates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.width, 4u);
  EXPECT_EQ(x->value.ToUint64(), 0xBu);
}

// The complementary direction at the initializer position: an unsigned
// initializer narrower than the declared target is zero-padded up to the
// declared width.
TEST(AssignmentExtensionTruncationSim, DeclarationInitializerExtendsUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] y = 4'hA;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

// §10.7 extends a narrower right-hand side by sign-extension when the RHS is
// signed. Here the signedness is carried by the built-in type — byte and int
// are signed by default (§6.11.1), with no explicit `signed` keyword — so a
// negative byte widened into an int replicates its sign bit across the added
// high bits.
TEST(AssignmentExtensionTruncationSim, BuiltinSignedTypeSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int wide;\n"
      "  byte narrow;\n"
      "  initial begin narrow = -8'sd3; wide = narrow; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* wide = f.ctx.FindVariable("wide");
  ASSERT_NE(wide, nullptr);

  EXPECT_EQ(wide->value.ToUint64(), 0xFFFFFFFDu);
}

// §10.7 states an implementation may, but need not, warn on an assignment size
// mismatch. This implementation takes the permissive path: a right-hand side
// wider than the left-hand side is accepted without an error and silently
// truncated, rather than being rejected during elaboration.
TEST(AssignmentExtensionTruncationSim, SizeMismatchAcceptedNotRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow = 32'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* narrow = f.ctx.FindVariable("narrow");
  ASSERT_NE(narrow, nullptr);

  EXPECT_EQ(narrow->value.ToUint64(), 0xDu);
}

}  // namespace
