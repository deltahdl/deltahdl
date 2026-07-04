#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CastOperatorElaboration, CastInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = int'(3.14);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, SignedCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = signed'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  initial void'(f());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] y;\n"
      "  assign y = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorSim, CastSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'hFF;\n"
      "    result = signed'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = -1;\n"
      "    result = unsigned'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastShortint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = 32'h1234ABCD;\n"
      "    result = shortint'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(TypeOperatorSim, TypeOpStructMemberWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] field_a;\n"
      "    logic [7:0] field_b;\n"
      "  } my_struct;\n"
      "  my_struct s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = 16'hCAFE;\n"
      "    result = s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(CastOperatorSim, CastConcatToShortint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint result;\n"
      "  initial result = shortint'({8'hFA, 8'hCE});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFACEu);
}

// 6.24.1: when the casting type is a constant expression giving the target
// width, that width shall be positive. A literal zero-width size cast is an
// error.
TEST(CastOperatorElaboration, SizeCastZeroWidthLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = 0'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: the zero-or-negative size rule applies to any constant-expression
// casting type, not just a bare literal. A constant expression that folds to
// zero ((2-2)) is likewise rejected.
TEST(CastOperatorElaboration, SizeCastZeroWidthConstExprError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = (2 - 2)'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: a positive constant-expression width is the legal, accepting form of
// the size cast; it must not be flagged by the zero-or-negative-size rule.
TEST(CastOperatorElaboration, SizeCastPositiveWidthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] r;\n"
      "  initial r = 4'(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 6.24.1: the expression inside a signing cast shall be an integral value. A
// real variable driven through signed'() has no bit representation and is
// rejected.
TEST(CastOperatorElaboration, RealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = signed'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: the integral-operand rule applies to unsigned'() as well as
// signed'(); a real variable inside unsigned'() is rejected.
TEST(CastOperatorElaboration, RealVarInUnsignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = unsigned'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: a real literal operand is likewise non-integral, so signed'(2.5) is
// rejected -- the operand need not be a declared variable to violate the rule.
TEST(CastOperatorElaboration, RealLiteralInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: the integral-operand rule also governs the size cast (changing the
// size), not only the signing casts. A real variable inside a numeric-width
// cast is rejected.
TEST(CastOperatorElaboration, RealVarInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: the integral-operand rule for a size cast rejects a real *literal*
// operand as well as a real variable -- a non-integral value is illegal
// regardless of how it is written.
TEST(CastOperatorElaboration, RealLiteralInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// 6.24.1: shortreal is a distinct non-integral operand type; a shortreal
// variable inside a signing cast is likewise rejected by the integral-operand
// rule.
TEST(CastOperatorElaboration, ShortrealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal s;\n"
      "  int r;\n"
      "  initial r = signed'(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(CastOperatorSim, CastByteTruncate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = byte'(32'hABCD);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

}  // namespace
