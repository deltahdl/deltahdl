#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringLiteralExpressionsSim, SingleCharStringLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] ch;\n"
      "  initial ch = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("ch");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41u);
}

TEST(StringLiteralExpressionsSim, MultiCharStringLiteralAsciiValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x4142u);
}

TEST(StringLiteralExpressionsSim, StringLiteralWidthIs8PerChar) {
  SimFixture f;
  auto* e1 = ParseExprFrom("\"A\"", f);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(EvalExpr(e1, f.ctx, f.arena).width, 8u);

  auto* e3 = ParseExprFrom("\"ABC\"", f);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(EvalExpr(e3, f.ctx, f.arena).width, 24u);
}

TEST(StringLiteralExpressionsSim, StringLiteralArithmeticAdd) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" + 8'd1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x42u);
}

TEST(StringLiteralExpressionsSim, StringLiteralBitwiseOr) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" | 8'h20", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x61u);
}

TEST(StringLiteralExpressionsSim, StringLiteralRelationalGreater) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"B\" > \"A\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 1u);
}

TEST(StringLiteralExpressionsSim, StringLiteralShiftLeft) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" << 1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x82u);
}

// A multi-character literal taking part in an operation is handled as one
// numeric value formed from all of its ASCII bytes, not byte-by-byte: "AB"
// is the 16-bit number 0x4142, so adding one yields 0x4143.
TEST(StringLiteralExpressionsSim, MultiCharStringLiteralActsAsSingleNumber) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"AB\" + 16'd1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x4143u);
}

// Left zero-padding of an oversized target must extend past a single 64-bit
// word: a 16-bit literal stored into an 80-bit vector keeps its bytes in the
// low word and leaves the entire upper word as padding zeros.
TEST(StringLiteralExpressionsSim, WideVectorPaddingSpansMultipleWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 80u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x4869ULL);
  EXPECT_EQ(var->value.words[1].aval, 0ULL);
}

// §11.10 with a literal built from §5.9's escape-sequence syntax: each escape
// contributes one 8-bit ASCII byte to the packed constant number, exactly like
// a plain character. "\t!" is the two bytes 0x09 (tab) and 0x21 ('!'), packed
// first-character-high into a 16-bit value 0x0921.
TEST(StringLiteralExpressionsSim,
     StringLiteralEscapeSequencesArePackedAsAscii) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"\\t!\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0921ULL);
}

// §11.10 defines left zero-padding only for a target larger than the literal;
// when the target is narrower, the assignment truncates (the §10.7 rule the
// clause defers to) rather than padding. "AB" is the 16-bit number 0x4142;
// stored into an 8-bit vector it keeps the low byte 0x42 ('B').
TEST(StringLiteralExpressionsSim, StringLiteralTruncatedIntoNarrowVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42ULL);
}

// A string literal is a constant number in a continuous-assignment context too,
// not only a procedural one: driving a net with "A" places the ASCII code 0x41
// on the net.
TEST(StringLiteralExpressionsSim, StringLiteralInContinuousAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41ULL);
}

// §11.10's worked example: a 14-character vector is loaded with an 11-character
// literal (left zero-padded, claim 4 + ASCII packing, claim 1), then the stored
// value is manipulated by the concatenation operator (claim 2) as a single
// numeric value (claim 3). Appending "!!!" (0x212121) and reassigning into the
// same 112-bit vector drops the three padding bytes off the top, leaving
// exactly the byte sequence the clause reports: 48656c6c6f20776f726c64212121.
TEST(StringLiteralExpressionsSim, HeadExampleConcatenateAndStore) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module string_test;\n"
      "  bit [8*14:1] stringvar;\n"
      "  initial begin\n"
      "    stringvar = \"Hello world\";\n"
      "    stringvar = {stringvar, \"!!!\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("stringvar");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 112u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x776f726c64212121ULL);
  EXPECT_EQ(var->value.words[1].aval, 0x48656c6c6f20ULL);
}

// §11.10: left zero-padding of an oversized target is consistent with the
// padding applied when a nonstring unsigned value is assigned. The string
// literal "Hi" and the plain unsigned number 16'h4869 carry the same bits, so
// storing each into an identical 32-bit vector must yield identical contents.
TEST(StringLiteralExpressionsSim, PaddingConsistentWithNonstringUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*4:1] a, b;\n"
      "  initial begin\n"
      "    a = \"Hi\";\n"
      "    b = 16'h4869;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x4869ULL);
  EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64());
}

}  // namespace
