#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>

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

TEST(ConstantExpressionElaboration, LocalparamOperandInConstantExpr) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam int L = 4;\n"
             "  parameter int P = L * 2;\n"
             "endmodule\n"));
}

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

const RtlirParamDecl* TopParam(const RtlirDesign* design,
                               std::string_view name) {
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == name) return &param;
  }
  return nullptr;
}

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

TEST(ConstantExpressionElaboration, DISABLED_TypeNameAsAnOperandIsReported) {
  for (const auto& [src, line] :
       {std::pair{"module t #(parameter type T = logic [7:0]);\n"
                  "  localparam int A = T + 1;\n"
                  "endmodule\n",
                  2},
        std::pair{"module t #(parameter type T = logic [7:0]);\n"
                  "  logic [T:0] r;\n"
                  "endmodule\n",
                  2},
        std::pair{"module t #(parameter type T = logic [7:0]);\n"
                  "  if (T) begin : g end\n"
                  "endmodule\n",
                  2},
        std::pair{"module t #(parameter type T = logic [7:0]);\n"
                  "  int v;\n"
                  "  initial v = T[1];\n"
                  "endmodule\n",
                  3},
        std::pair{"module t;\n"
                  "  typedef logic [3:0] n_t;\n"
                  "  localparam int B = n_t[1];\n"
                  "endmodule\n",
                  3},
        std::pair{"class C #(type T = int);\n"
                  "  typedef int t;\n"
                  "  function int f(); return t + T; endfunction\n"
                  "endclass\n"
                  "module m; endmodule\n",
                  3},
        std::pair{"package pk; typedef int t; endpackage\n"
                  "module t;\n"
                  "  localparam int A = pk::t + 1;\n"
                  "endmodule\n",
                  3},
        std::pair{"typedef int u_t;\n"
                  "module t;\n"
                  "  localparam int B = u_t[3:0];\n"
                  "endmodule\n",
                  3},
        std::pair{"class C; typedef int t; endclass\n"
                  "module t;\n"
                  "  localparam int D = C::t + 1;\n"
                  "endmodule\n",
                  3}}) {
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "names a type, not a value",
                              line, "11.2"))
        << src;
  }
}

TEST(ConstantExpressionElaboration, TypeOperatorsOfATypeNameAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t #(parameter type T = logic [7:0]);\n"
      "  localparam int B = $bits(T);\n"
      "  localparam int V = T'(5);\n"
      "  localparam bit E = type(T) == type(logic [7:0]);\n"
      "  localparam string N = $typename(T);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
