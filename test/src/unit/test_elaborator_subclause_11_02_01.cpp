#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
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
  EXPECT_TRUE(IsConstantSysFunc("$timeunit"));
  EXPECT_TRUE(IsConstantSysFunc("$timeprecision"));
}

// §11.2.1 counts §20.4's timescale functions among the constant system
// functions, so a parameter may take its value from either.
TEST(ConstantExpressionElaboration, TimescaleFunctionsInitializeLocalparams) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam int U = $timeunit;\n"
             "  localparam int P = $timeprecision;\n"
             "endmodule\n"));
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
// elaboration: such a call in a constant expression is evaluated while
// elaborating. §6.19.5.5 decides the value the call folds to, since num()
// returns how many elements the enumeration has. `color_t` declares RED, GREEN
// and BLUE, so `N` resolves to 3. No other quantity in this source is 3, so a
// fold that read some other count would not reach the same answer.
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

// §11.2.1 requires the fold wherever a constant expression is required, and not
// only where a localparam initializer asks for a value: such a call in a
// constant expression is evaluated while elaborating. A packed range is such a
// place, so `S.len()*8-1:0` sizes `v` at elaboration time. §6.16.1 makes
// `S.len()` 3, so the range is [23:0] and `v` is 24 bits.
//
// 24 is not a default. A range whose bounds did not fold leaves the width at
// the 1 `RtlirVariable::width` initializes to, and no other quantity in this
// source is 24: the string is three characters and the multiplier is 8, so only
// the folded product reaches it.
TEST(ConstantExpressionElaboration, StringParameterLenSizesAPackedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abc\";\n"
      "  logic [S.len()*8-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirVariable* v = nullptr;
  for (const auto& var : design->top_modules[0]->variables) {
    if (var.name == "v") v = &var;
  }
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 24U);
}

// §11.2.1 makes `c.num()` a constant built-in method call although `c` is a
// variable and not a constant expression. The clause rules that built-in
// methods whose result never depends on what the identifier currently holds
// count as constant built-in method calls once their input arguments are
// constant expressions, constant identifier or not. §6.19.5.5 makes num() such
// a method, because the number of elements in an enumeration is fixed by the
// declaration of `color_t` rather than by what `c` holds. §7.2.2 requires a
// struct member default to be a constant expression, so this source is accepted
// and nothing is reported.
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

// §5.13 ties each built-in method to a particular data type, and it associates
// size() with a dynamic array. No built-in method is associated with an
// integer, so `P.size()` names no built-in method call and §11.2.1 admits it
// nowhere a constant expression is required. §7.2.2 requires a struct member
// default to be a constant expression, so the declaration is rejected. Before
// the fix nothing was reported and the member's value was left unresolved.
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

// §11.7 has $signed and $unsigned evaluate the input expression and return a
// one-dimensional packed array of its width and value, with the signedness the
// function names, so `$unsigned(4'b1100)` is four bits wide and not thirty-two.
// A specparam is what makes that inferred width observable: §6.20.5 gives a
// specparam with no range specification the range of its final value, and
// Elaborator::ElaborateSpecparam in src/elaborator/elaborator_items.cpp takes
// RtlirVariable::width from InferExprWidth, so the width recorded for `tW` is
// the width the signing conversion was inferred to have.
//
// 4 is not a default here. A width that did not come from the operand is the
// 32 InferExprWidth answers for every other system function, which is what this
// case read before the fix.
TEST(ConstantExpressionElaboration,
     SigningConversionSpecparamTakesOperandWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specparam tW = $unsigned(4'b1100);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* tw = nullptr;
  for (const auto& var : design->top_modules[0]->variables) {
    if (var.name == "tW") tw = &var;
  }
  ASSERT_NE(tw, nullptr);
  EXPECT_EQ(tw->width, 4U);
}

// The value parameter `name` of the top module `design` elaborated, or null.
const RtlirParamDecl* TopParam(const RtlirDesign* design,
                               std::string_view name) {
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == name) return &param;
  }
  return nullptr;
}

// §11.2.1 admits a built-in method call into a constant expression only when
// it has no side effects and its value depends on its arguments and, where the
// identifier is constant, that identifier's value. pop_front() changes its
// queue, and next() reads the current value of a variable that is no constant,
// so neither is a constant expression.
TEST(ConstantExpressionElaboration,
     MutatingAndValueReadingMethodsAreNotConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int q[$];\n"
      "  typedef struct {\n"
      "    int a = q.pop_front();\n"
      "    int b = c.next();\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "struct member default value must be a constant "
                            "expression",
                            5, "7.2.2"));
}

// §11.2.1 has a constant built-in method call evaluated at elaboration. last()
// does not depend on the variable it is called on, so it is constant on one,
// and getc() on a string parameter is constant with a constant index. C is
// the last of three members and 'a' is 97, values no fold that gave up
// reaches.
TEST(ConstantExpressionElaboration, EnumLastAndStringGetcFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B, C} e_t;\n"
      "  e_t e;\n"
      "  localparam string S = \"ab\";\n"
      "  localparam int K = 1;\n"
      "  localparam int L = e.last();\n"
      "  localparam int F = e.first();\n"
      "  localparam int G = S.getc(0);\n"
      "  localparam int H = S.getc(K);\n"
      "  localparam int Z = S.getc(5);\n"
      "  localparam int N = S.getc(-1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const struct {
    std::string_view name;
    int64_t value;
  } kWant[] = {{"L", 2}, {"F", 0}, {"G", 97}, {"H", 98}, {"Z", 0}, {"N", 0}};
  for (const auto& want : kWant) {
    const RtlirParamDecl* p = TopParam(design, want.name);
    ASSERT_NE(p, nullptr) << want.name;
    EXPECT_TRUE(p->is_resolved) << want.name;
    EXPECT_EQ(p->resolved_value, want.value) << want.name;
  }
}

// A pure built-in method this implementation does not evaluate at elaboration
// is reported where a constant expression is required, rather than leaving the
// declaration without a value, and so is getc() written on what is no string
// parameter or without its one argument.
TEST(ConstantExpressionElaboration, UnfoldedBuiltinMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"ab\";\n"
      "  localparam int X = 5;\n"
      "  localparam int I = S.atoi();\n"
      "  localparam int J = X.getc(0);\n"
      "  localparam int K = S.getc;\n"
      "  localparam int M = S.getc();\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "initializer is not a constant expression", line,
                              "6.20.4"));
  }
}

// §5.13 lets a built-in method with no arguments drop its parentheses, so
// `e.first` and `e.num` are the calls `e.first()` and `e.num()`.
TEST(ConstantExpressionElaboration, ParenthesisFreeEnumMethodsFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B, C} e_t;\n"
      "  e_t e;\n"
      "  localparam int F = e.last;\n"
      "  localparam int N = e.num;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirParamDecl* last = TopParam(design, "F");
  const RtlirParamDecl* num = TopParam(design, "N");
  ASSERT_NE(last, nullptr);
  ASSERT_NE(num, nullptr);
  EXPECT_EQ(last->resolved_value, 2);
  EXPECT_EQ(num->resolved_value, 3);
}

// §11.2.1 with A.8.4: a constant expression reaches a parameter by its own
// name or a package's, never by a hierarchical one, so a declaration's packed
// or unpacked range written with one is reported -- it was folded to nothing
// and the vector made one bit wide -- while a range reading a package's
// parameter, a built-in method of a variable, or $bits of one is constant.
TEST(ConstantExpressionElaboration, HierarchicalReferenceInARangeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  parameter int PW = 3;\n"
      "endpackage\n"
      "typedef enum {A, B, C} e_t;\n"
      "module mon #(parameter int W = 4) ();\n"
      "endmodule\n"
      "module cpu;\n"
      "  mon #(.W(8)) r();\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "  e_t e;\n"
      "  logic [c.r.W:0] v;\n"
      "  logic [1:0][c.r.W:0] w;\n"
      "  logic u [c.r.W];\n"
      "  logic [pk::PW:0] ok1;\n"
      "  logic [e.num():0] ok2;\n"
      "  logic [$bits(e):0] ok3;\n"
      "endmodule\n",
      f);
  const char* message = "contains a hierarchical reference, which is no";
  for (uint32_t line : {13u, 14u, 15u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "11.2.1"))
        << line;
  }
  for (uint32_t line : {16u, 17u, 18u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), message, line, "11.2.1"))
        << line;
  }
}

}  // namespace
