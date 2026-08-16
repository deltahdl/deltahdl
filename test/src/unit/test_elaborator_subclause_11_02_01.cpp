#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstantExpressionElaboration, ConstantTernaryInParamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 1 ? 10 : 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, ScopedUnresolved) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("UNKNOWN", f), scope), std::nullopt);
}

TEST(ConstantExpressionElaboration, BinaryExprInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 3 + 4;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, DependentParamsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int WIDTH = 8;\n"
             "  parameter int DEPTH = 2 ** WIDTH;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConstantSysFuncInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = $clog2(256);\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConcatenationInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] P = {4'd3, 4'd5};\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ReplicationInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [3:0] P = {4{1'b1}};\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, UnaryExprInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = -42;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, StringLiteralInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter string S = \"hello\";\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, NestedSysFuncInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = $clog2($bits(logic [31:0]));\n"
             "endmodule\n"));
}

TEST(ConstEval, ScopedConcatenationEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4'd3, 4'd5}", f)), 0x35);
}

TEST(ConstEval, ScopedReplicationEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

TEST(ConstEval, ScopedSysFuncEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
}

TEST(ConstEvalReal, RealLiteralEvaluation) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("3.14", f));
  ASSERT_TRUE(val.has_value());
  if (val.has_value()) {
    EXPECT_DOUBLE_EQ(*val, 3.14);
  }
}

TEST(ConstEvalReal, RealBinaryEvaluation) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("1.5 + 2.5", f));
  ASSERT_TRUE(val.has_value());
  if (val.has_value()) {
    EXPECT_DOUBLE_EQ(*val, 4.0);
  }
}

TEST(ConstEvalReal, IntPromotesToReal) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("42", f));
  ASSERT_TRUE(val.has_value());
  if (val.has_value()) {
    EXPECT_DOUBLE_EQ(*val, 42.0);
  }
}

TEST(ConstEvalReal, DivisionByZeroReturnsNullopt) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("1.0 / 0.0", f));
  EXPECT_FALSE(val.has_value());
}

// §11.2.1 exposes the constant-system-function whitelist so §13.4.3 can apply
// the same admissibility rule when validating the body of a constant function.
// Spot-check one entry from each family the LRM lists: math, conversion,
// bit-vector, timescale, $sformatf. Non-pure sys funcs (e.g. $time) must be
// rejected.
TEST(ConstantSysFuncWhitelist, MathFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$clog2"));
  EXPECT_TRUE(IsConstantSysFunc("$sqrt"));
}

TEST(ConstantSysFuncWhitelist, ConversionFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$signed"));
  EXPECT_TRUE(IsConstantSysFunc("$itor"));
}

TEST(ConstantSysFuncWhitelist, BitVectorFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$countones"));
  EXPECT_TRUE(IsConstantSysFunc("$onehot"));
}

TEST(ConstantSysFuncWhitelist, TimescaleFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$timescale"));
  EXPECT_TRUE(IsConstantSysFunc("$timeprecision"));
}

TEST(ConstantSysFuncWhitelist, SformatfAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$sformatf"));
}

TEST(ConstantSysFuncWhitelist, ImpureFunctionRejected) {
  EXPECT_FALSE(IsConstantSysFunc("$time"));
  EXPECT_FALSE(IsConstantSysFunc("$display"));
  EXPECT_FALSE(IsConstantSysFunc("$random"));
}

// §11.2.1: constant bit-selects and part-selects of parameters are listed
// among the legal operands of a constant expression. Make sure the
// elaborator accepts a parameter whose value is computed from a bit-select
// of another parameter.
TEST(ConstantExpressionElaboration, ConstantBitSelectOfParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] BASE = 8'b1010_1100;\n"
             "  parameter logic       BIT  = BASE[5];\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConstantPartSelectOfParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] BASE  = 8'b1010_1100;\n"
             "  parameter logic [3:0] NIBBLE = BASE[7:4];\n"
             "endmodule\n"));
}

// §7.2.2 requires a struct member default to be a constant expression, and
// §11.2.1 decides what one is. `q` is a queue, so §7.10.2.1's size() returns
// the current number of items in the queue and depends on the queue's value,
// which leaves the default non-constant and the declaration rejected. Before
// the fix nothing was reported and the member's value was left unresolved.
//
// The report stands at the typedef's own line rather than at the member's,
// as it does for every typedef case in
// test/src/unit/test_elaborator_subclause_07_02_02.cpp.
TEST(ConstantExpressionElaboration, QueueSizeInStructMemberDefaultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$];\n"
      "  typedef struct {\n"
      "    int a = q.size();\n"
      "    int b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "struct member default value must be a constant "
                            "expression",
                            3, "7.2.2"));
}

// §11.2.1: a localparam is an admitted constant-expression operand, resolved on
// a different production path than a parameter.
TEST(ConstantExpressionElaboration, LocalparamOperandInConstantExpr) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam int L = 4;\n"
             "  parameter int P = L * 2;\n"
             "endmodule\n"));
}

// §11.2.1: a genvar is an admitted constant-expression operand within a
// generate loop.
TEST(ConstantExpressionElaboration, GenvarOperandInConstantExpr) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  genvar g;\n"
             "  generate\n"
             "    for (g = 0; g < 2; g = g + 1) begin : blk\n"
             "      localparam int L = g + 1;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

// §11.2.1 requires that a constant built-in method call be folded during
// elaboration: "when used in constant expressions, these function calls shall
// be evaluated at elaboration time". §6.19.5.5 decides the value the call
// folds to, since "The num() method returns the number of elements in the
// given enumeration". `color_t` declares RED, GREEN and BLUE, so `N` resolves
// to 3. No other quantity in this source is 3, so a fold that read some other
// count would not reach the same answer.
TEST(ConstantExpressionElaboration, EnumNumFoldsToTheMemberCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "  color_t c;\n"
      "  localparam int N = c.num();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

// §11.2.1 makes `c.num()` a constant built-in method call although `c` is a
// variable and not a constant expression. The clause rules that built-in
// methods "whose value does not depend on the current value of the identifier
// are constant built-in method calls if the input arguments are constant
// expressions even when the identifier is not constant". §6.19.5.5 makes
// num() such a method, because the number of elements in an enumeration is
// fixed by the declaration of `color_t` rather than by what `c` holds. §7.2.2
// requires a struct member default to be a constant expression, so this
// source is accepted and nothing is reported.
TEST(ConstantExpressionElaboration, EnumNumIsConstantWhereTheIdentifierIsNot) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "  color_t c;\n"
      "  typedef struct {\n"
      "    int a = c.num();\n"
      "    int b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §5.13 rules that "a built-in method can only be associated with a particular
// data type", and it associates size() with a dynamic array. No built-in
// method is associated with an integer, so `P.size()` names no built-in method
// call and §11.2.1 admits it nowhere a constant expression is required. §7.2.2
// requires a struct member default to be a constant expression, so the
// declaration is rejected. Before the fix nothing was reported and the
// member's value was left unresolved.
//
// The report stands at the typedef's own line, which is line 3 of this source,
// rather than at the member's line 4. That is where
// ConstantExpressionElaboration.QueueSizeInStructMemberDefaultIsReported above
// reads it too.
TEST(ConstantExpressionElaboration,
     IntegerParameterSizeInStructMemberDefaultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam int P = 4;\n"
      "  typedef struct {\n"
      "    int a = P.size();\n"
      "    int b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "struct member default value must be a constant "
                            "expression",
                            3, "7.2.2"));
}

}  // namespace
