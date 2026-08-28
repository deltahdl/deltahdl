#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(SignedExprElaboration, SignedInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = $signed(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SignedExprElaboration, UnsignedInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic signed [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = $unsigned(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SignedExprElaboration, SignedInContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  wire signed [7:0] y;\n"
      "  assign y = $signed(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SignedExprElaboration, UnsignedInExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic [7:0] y;\n"
      "  initial y = $unsigned(a) + $unsigned(b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SignedExprElaboration, NestedSignedUnsignedElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  initial b = $signed($unsigned(a));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.7: the `$signed` and `$unsigned` system functions "shall evaluate the
// input expression and return a one-dimensional packed array with the same
// number of bits and value of the input expression and the signedness defined
// by the function". A signing conversion is therefore as wide as its operand,
// so `$signed(4'b1100)` is four bits rather than the thirty-two bits an
// ordinary system function's integer result has. §11.7 gives the two spellings
// of the conversion one example and one value, so the cast spelling is
// asserted beside the system-function spelling: the width of `$signed(...)`
// alone would not say that the two spellings agree.
TEST(SignedExprElaboration,
     SignedSystemFunctionAndSignedCastAreBothFourBitsWide) {
  TypedefMap typedefs;
  Expr operand;
  operand.kind = ExprKind::kIntegerLiteral;
  operand.text = "4'b1100";

  Expr call;
  call.kind = ExprKind::kSystemCall;
  call.callee = "$signed";
  call.args = {&operand};

  Expr cast;
  cast.kind = ExprKind::kCast;
  cast.text = "signed";
  cast.lhs = &operand;

  EXPECT_EQ(InferExprWidth(&call, typedefs), 4u);
  EXPECT_EQ(InferExprWidth(&cast, typedefs), 4u);
}

// §11.7: `$signed` returns "a one-dimensional packed array with the same
// number of bits and value of the input expression", so an elaborator check
// that measures `$signed(4'b1100)` counts four bits. This is that count where
// a caller writes it down: ElaboratorOperationRules::CheckBitStreamCastExpr in
// src/elaborator/elaborator_validate_operations_streaming.cpp sizes the source
// of a bit-stream cast through InferExprWidth, and §6.24.3 has it reject a
// cast between fixed-size types of different sizes whose destination is
// unpacked, naming both widths in the report. Sizing the conversion at
// thirty-two bits puts the wrong number in that sentence.
TEST(SignedExprElaboration,
     BitStreamCastReportsFourBitsForASignedSystemFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte arr2_t [2];\n"
      "  arr2_t a;\n"
      "  initial a = arr2_t'($signed(4'b1100));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (4 bits to 16 bits) with an "
                            "unpacked destination is illegal",
                            4, "6.24.3"));
}

}  // namespace
