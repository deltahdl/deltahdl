#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

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

TEST(SignedExprElaboration, RealVarInSignedSystemFunctionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = $signed(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$signed works only on an integral value", 4,
                            "11.7"));
}

TEST(SignedExprElaboration, RealVarInUnsignedSystemFunctionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = $unsigned(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$unsigned works only on an integral value", 4,
                            "11.7"));
}

TEST(SignedExprElaboration, RealLiteralArgumentToSignedSystemFunctionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial r = $signed(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$signed works only on an integral value", 3,
                            "11.7"));
}

TEST(SignedExprElaboration, ShortrealVarInUnsignedSystemFunctionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal s;\n"
      "  int r;\n"
      "  initial r = $unsigned(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$unsigned works only on an integral value", 4,
                            "11.7"));
}

TEST(SignedExprElaboration, TimeLiteralArgumentToSignedSystemFunctionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  int r;\n"
      "  initial r = $signed(2.1ns);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$signed works only on an integral value", 4,
                            "11.7"));
}

}  // namespace
