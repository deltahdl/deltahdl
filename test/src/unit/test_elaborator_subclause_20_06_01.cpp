#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, TypenameRejectsHierarchicalRef) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  logic x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  parameter integer T = $typename(s.x);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument is a hierarchical reference",
                    6, "20.6.1"));
}

TEST(SubroutineCallExprElaboration,
     TypenameRejectsHierarchicalRefInLocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  logic x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  localparam integer T = $typename(s.x);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument is a hierarchical reference",
                    6, "20.6.1"));
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsLocalReference) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  parameter integer T = $typename(x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameWithoutArgsInParamInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer T = $typename();\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
}

TEST(SubroutineCallExprElaboration, TypenameRejectsDynamicArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  parameter integer T = $typename(d[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument selects an element of a dynamic object",
                    3, "20.6.1"));
}

TEST(SubroutineCallExprElaboration, TypenameRejectsAssocArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[string];\n"
      "  parameter integer T = $typename(a[\"k\"]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument selects an element of a dynamic object",
                    3, "20.6.1"));
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsStaticArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int s[2];\n"
      "  parameter integer T = $typename(s[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsScalarBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  parameter integer T = $typename(v[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypenameConstEval, ABuiltinTypeFoldsToItsKeyword) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(int)", f)), "int");
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(real)", f)), "real");
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(string)", f)), "string");
}

TEST(TypenameConstEval, OtherArgumentsAreNotFolded) {
  EvalFixture f;
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename(w)", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(1 + 2)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$clog2(int)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename()", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(struct packed { bit a; })", f))
          .has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(bit [W:0])", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename(~w)", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(w[0])", f)).has_value());
}

std::string_view FoldedChars(RtlirDesign* design, std::string_view name) {
  const RtlirParamDecl* pd = FindParam(design, "top", name);
  return pd == nullptr ? "<no parameter>" : pd->resolved_string;
}

TEST(TypenameConstEval, ATypeNodeFoldsToItsName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam string A = $typename(int unsigned);\n"
      "  localparam string B = $typename(bit signed [3:0]);\n"
      "  localparam string C = $typename(struct packed { bit a; byte b; });\n"
      "  localparam string D = $typename(enum bit [1:0] { X, Y = 3 });\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "int unsigned");
  EXPECT_EQ(FoldedChars(design, "B"), "bit signed[3:0]");
  EXPECT_EQ(FoldedChars(design, "C"), "struct packed{bit a;byte b;}top.s$type");
  EXPECT_EQ(FoldedChars(design, "D"), "enum{X=2'd0,Y=2'd3}top.e$type");
}

TEST(TypenameConstEval, ARangedKeywordFoldsWithItsBounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam int W = 8;\n"
      "  localparam string A = $typename(bit [3:0]);\n"
      "  localparam string B = $typename(logic [W-1:0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "bit[3:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "logic[7:0]");
}

TEST(TypenameConstEval, ATypedefNameFoldsToTheTypeItNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit node;\n"
      "  typedef struct { bit A; bit B; } AB_t;\n"
      "  localparam string A = $typename(node);\n"
      "  localparam string B = $typename(AB_t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "bit");
  EXPECT_EQ(FoldedChars(design, "B"), "struct{bit A;bit B;}top.AB_t");
}

TEST(TypenameConstEval, AnExpressionFoldsToItsSelfDeterminedType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct { bit A; bit B; } AB_t;\n"
      "  logic [7:0] v;\n"
      "  bit [3:0] w;\n"
      "  AB_t AB [10];\n"
      "  int m [2][3];\n"
      "  typedef enum { X, Y } e_t;\n"
      "  localparam string A = $typename(v);\n"
      "  localparam string B = $typename(AB);\n"
      "  localparam string C = $typename(AB[0]);\n"
      "  localparam string D = $typename(v[0]);\n"
      "  localparam string E = $typename(v + w);\n"
      "  localparam string F = $typename(w + 1.5);\n"
      "  localparam string G = $typename(m[0]);\n"
      "  localparam string H = $typename(v[5-:2]);\n"
      "  localparam string I = $typename(X[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "struct{bit A;bit B;}top.AB_t$[0:9]");
  EXPECT_EQ(FoldedChars(design, "C"), "struct{bit A;bit B;}top.AB_t");
  EXPECT_EQ(FoldedChars(design, "D"), "logic");
  EXPECT_EQ(FoldedChars(design, "E"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "F"), "real");
  EXPECT_EQ(FoldedChars(design, "G"), "int$[0:2]");
  EXPECT_EQ(FoldedChars(design, "H"), "logic[1:0]");
  EXPECT_EQ(FoldedChars(design, "I"), "bit");
}

TEST(TypenameConstEval, ASelectOfAPackedArrayFoldsToItsElementsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0][7:0] p;\n"
      "  bit [3:0] n;\n"
      "  localparam string A = $typename(p[1]);\n"
      "  localparam string B = $typename(p[2:1]);\n"
      "  localparam string C = $typename(p[1] + n);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "logic[15:0]");
  EXPECT_EQ(FoldedChars(design, "C"), "logic[7:0]");
}

TEST(TypenameConstEval, ASelectOfATypedefsPackedArrayFoldsToItsElementsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic [3:0][7:0] w_t;\n"
      "  w_t q;\n"
      "  bit [3:0] n;\n"
      "  localparam string A = $typename(q[1]);\n"
      "  localparam string B = $typename(q[2:1]);\n"
      "  localparam string C = $typename(q[1] + n);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "logic[15:0]");
  EXPECT_EQ(FoldedChars(design, "C"), "logic[7:0]");
}

TEST(TypenameConstEval, WhatTheModuleCannotResolveIsLeftUnfolded) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit w_t;\n"
      "endpackage\n"
      "module top;\n"
      "  class K;\n"
      "  endclass\n"
      "  typedef enum { X, Y } e_t;\n"
      "  K h;\n"
      "  p::w_t pw;\n"
      "  real r;\n"
      "  string s;\n"
      "  int q [2];\n"
      "  int m [2][3];\n"
      "  localparam string A = $typename(h);\n"
      "  localparam string B = $typename(pw);\n"
      "  localparam string C = $typename(X);\n"
      "  localparam string D = $typename(-r);\n"
      "  localparam string E = $typename({s});\n"
      "  localparam string F = $typename(q[1:0]);\n"
      "  localparam string G = $typename(m[1][2]);\n"
      "  localparam string H = $typename(type(r));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  for (std::string_view name : {"A", "B", "C", "D", "E", "F", "G", "H"}) {
    EXPECT_EQ(FoldedChars(design, name), "") << name;
  }
}

TEST(TypenameArguments, DISABLED_NoArgumentOrTwoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  parameter string P = $typename();\n"
      "  initial $display(\"%s\", $typename());\n"
      "  initial $display(\"%s\", $typename(a, b));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "$typename takes exactly one argument", line,
                              "20.6.1"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(TypenameArguments, OneExpressionOrOneTypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  parameter string P = $typename(a);\n"
             "  initial $display(\"%s %s\", $typename(a), $typename(int));\n"
             "endmodule\n"));
}

constexpr const char* kTypenameConstantMessage =
    "$typename cannot serve as an elaboration-time constant ";

TEST(SubroutineCallExprElaboration,
     DISABLED_TypenameRejectsAQueueElementAndAHandleProperty) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int p;\n"
      "endclass\n"
      "module m;\n"
      "  int q[$];\n"
      "  C h;\n"
      "  parameter string T = $typename(q[0]);\n"
      "  parameter string U = $typename(h.p);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string(kTypenameConstantMessage) +
                                  "when its argument selects an element of a "
                                  "dynamic object",
                              line, "20.6.1"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(SubroutineCallExprElaboration,
     DISABLED_TypenameAcceptsAMemberOfALocalStruct) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct {logic [3:0] f;} st_t;\n"
             "  st_t st;\n"
             "  parameter string T = $typename(st.f);\n"
             "endmodule\n"));
}

TEST(SubroutineCallExprElaboration,
     DISABLED_TypenameRejectsAHierarchicalReferenceInEveryConstantContext) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  logic x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  logic [$typename(s.x) == \"logic\" : 0] pd;\n"
      "  logic ud [$typename(s.x) == \"logic\" : 0];\n"
      "  if ($typename(s.x) == \"logic\") begin : g1\n"
      "  end\n"
      "  case ($typename(s.x) == \"logic\")\n"
      "    1: begin : g2 end\n"
      "    default: begin : g3 end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < ($typename(s.x) == \"logic\"); i++) begin : "
      "g4\n"
      "  end\n"
      "  localparam bit L = $typename(s.x) == \"logic\";\n"
      "endmodule\n",
      f, "top");
  for (uint32_t line : {6u, 7u, 8u, 10u, 14u, 16u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string(kTypenameConstantMessage) +
                                  "when its argument is a hierarchical "
                                  "reference",
                              line, "20.6.1"))
        << "line " << line;
  }
}

TEST(
    SubroutineCallExprElaboration,
    DISABLED_TypenameRejectsAHierarchicalReferenceInPackageInterfaceAndProgram) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  parameter string P = $typename(top.x);\n"
      "endpackage\n"
      "interface I;\n"
      "  parameter string P = $typename(top.x);\n"
      "endinterface\n"
      "program G;\n"
      "  parameter string P = $typename(top.x);\n"
      "endprogram\n"
      "module top;\n"
      "  logic x;\n"
      "  I i();\n"
      "  G g();\n"
      "endmodule\n",
      f, "top");
  for (uint32_t line : {2u, 5u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string(kTypenameConstantMessage) +
                                  "when its argument is a hierarchical "
                                  "reference",
                              line, "20.6.1"))
        << "line " << line;
  }
}

TEST(SubroutineCallExprElaboration,
     TypenameAcceptsAHierarchicalReferenceOutsideAConstant) {
  EXPECT_TRUE(
      ElabOk("module sub;\n"
             "  logic x;\n"
             "endmodule\n"
             "module top;\n"
             "  sub s();\n"
             "  int q[$];\n"
             "  initial $display(\"%s %s\", $typename(s.x), $typename(q[0]));\n"
             "endmodule\n"));
}

TEST(TypenameConstEval, DISABLED_EveryKindOfOperandFoldsToItsName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit w_t;\n"
      "endpackage\n"
      "module top;\n"
      "  class K; endclass\n"
      "  typedef enum {X, Y} e_t;\n"
      "  K h;\n"
      "  p::w_t pw;\n"
      "  real r;\n"
      "  string s;\n"
      "  int q[2];\n"
      "  int m[2][3];\n"
      "  localparam string A = $typename(h);\n"
      "  localparam string B = $typename(pw);\n"
      "  localparam string C = $typename(X);\n"
      "  localparam string D = $typename(-r);\n"
      "  localparam string E = $typename({s});\n"
      "  localparam string F = $typename(q[0:1]);\n"
      "  localparam string G = $typename(m[1][2]);\n"
      "  localparam string H = $typename(type(r));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "top.K");
  EXPECT_EQ(FoldedChars(design, "B"), "bit");
  EXPECT_EQ(FoldedChars(design, "C"), "enum{X=32'sd0,Y=32'sd1}top.e_t");
  EXPECT_EQ(FoldedChars(design, "D"), "real");
  EXPECT_EQ(FoldedChars(design, "E"), "string");
  EXPECT_EQ(FoldedChars(design, "F"), "int$[0:1]");
  EXPECT_EQ(FoldedChars(design, "G"), "int");
  EXPECT_EQ(FoldedChars(design, "H"), "real");
}

TEST(TypenameConstEval, AWholeMultidimensionalArrayFoldsWithEveryRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int m[2][3];\n"
      "  localparam string M = $typename(m);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "M"), "int$[0:1][0:2]");
}

TEST(TypenameConstEval, DISABLED_AVariablySizedArrayFoldsWithItsDimension) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int d[];\n"
      "  int q[$];\n"
      "  int a[string];\n"
      "  int w[*];\n"
      "  int i[int];\n"
      "  localparam string D = $typename(d);\n"
      "  localparam string Q = $typename(q);\n"
      "  localparam string A = $typename(a);\n"
      "  localparam string W = $typename(w);\n"
      "  localparam string I = $typename(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "D"), "int$[]");
  EXPECT_EQ(FoldedChars(design, "Q"), "int$[$]");
  EXPECT_EQ(FoldedChars(design, "A"), "int$[string]");
  EXPECT_EQ(FoldedChars(design, "W"), "int$[*]");
  EXPECT_EQ(FoldedChars(design, "I"), "int$[int]");
}

}  // namespace
