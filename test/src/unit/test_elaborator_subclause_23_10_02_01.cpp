#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"

using namespace delta;

namespace {

TEST(OrderedListParameterAssignment, PositionalValuesMapInDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 15);
}

TEST(OrderedListParameterAssignment,
     SinglePositionalValueOverridesFirstParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(42) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 42);
}

TEST(OrderedListParameterAssignment,
     PartialSubsetKeepsTrailingParametersAtDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3,\n"
      "               parameter int C = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].resolved_value, 3);
  EXPECT_EQ(u0->params[2].resolved_value, 4);
}

TEST(OrderedListParameterAssignment, EmptyOrderedListKeepsAllDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 7,\n"
      "               parameter int B = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #() u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 7);
  EXPECT_EQ(u0->params[1].resolved_value, 9);
}

TEST(OrderedListParameterAssignment, TooManyPositionalValuesRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "too many positional parameter overrides for module 'child'", 4,
      "23.10.2.1"));
}

TEST(OrderedListParameterAssignment,
     LocalparamInParameterPortListExcludedFromOrderedList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 10,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5, 6) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  for (const auto& p : u0->params) {
    if (p.name == "A") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 5);
    } else if (p.name == "L") {
      EXPECT_TRUE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 10);
    } else if (p.name == "B") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 6);
    }
  }
}

TEST(OrderedListParameterAssignment,
     OrderedListCountedAgainstNonLocalparamsOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 99,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(7, 8, 9) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many positional parameter overrides for "
                            "module 'child': 3 provided, 2 allowed",
                            6, "23.10.2.1"));
}

TEST(OrderedListParameterAssignment,
     PositionalOverrideValueFromInstantiatingParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int P = 12;\n"
      "  child #(P) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 12);
}

TEST(OrderedListParameterAssignment,
     PositionalOverrideValueFromInstantiatingLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int Q = 20;\n"
      "  child #(Q) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 20);
}

TEST(OrderedListParameterAssignment,
     PositionalTypeParameterOverrideAppliesInDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(shortint) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_GE(u0->variables.size(), 1u);
  EXPECT_EQ(u0->variables[0].name, "x");
  EXPECT_EQ(u0->variables[0].width, 16u);
}

RtlirDesign* ElaborateBodyParamInstance(std::string_view items,
                                        std::string_view assignment,
                                        ElabFixture& f) {
  std::string src = "module m;\n";
  src += items;
  src += "endmodule\nmodule top;\n  m #(";
  src += assignment;
  src += ") u();\nendmodule\n";
  return ElaborateSrc(src, f, "top");
}

int64_t BodyParamUnder(std::string_view items, std::string_view assignment,
                       std::string_view name, ElabFixture& f) {
  auto* design = ElaborateBodyParamInstance(items, assignment, f);
  return design == nullptr ? -1 : ParamValue(design, name);
}

TEST(BodyParameterAssignment, NamedAssignmentReachesAParameterAmongTheItems) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  localparam int Q = P;\n",
                           ".P(5)", "Q", f),
            5);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment, OrderedAssignmentReachesAParameterAmongTheItems) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  localparam int Q = P;\n", "5",
                           "Q", f),
            5);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment,
     OrderedValuesBindToBodyParametersInDeclarationOrder) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter A = 1;\n  parameter B = 2;\n"
                           "  localparam int Q = A * 10 + B;\n",
                           "3, 4", "Q", f),
            34);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment, DependentBodyParameterIsRefoldedWithTheOverride) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  parameter D = P * 2;\n",
                           ".P(5)", "D", f),
            10);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment,
     OverrideIsConvertedToARangeWrittenAsAnEarlierOverriddenBodyParameter) {
  const std::string_view kItems =
      "  parameter int TOP = 15;\n  parameter logic [TOP:0] P = 0;\n"
      "  localparam int Q = P;\n  localparam int B = $bits(P);\n";
  ElabFixture fq;
  EXPECT_EQ(BodyParamUnder(kItems, ".TOP(7), .P(16'hABCD)", "Q", fq), 0xCD);
  EXPECT_FALSE(fq.has_errors);
  ElabFixture fb;
  EXPECT_EQ(BodyParamUnder(kItems, ".TOP(7), .P(16'hABCD)", "B", fb), 8);
}

TEST(BodyParameterAssignment, NamedAssignmentToABodyLocalparamIsRejected) {
  ElabFixture f;
  BodyParamUnder("  localparam int L = 1;\n", ".L(5)", "L", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' has no parameter 'L'", 5, "23.10.2.2"));
}

TEST(BodyParameterAssignment,
     BodyParameterUnderAParameterPortListIsNotAssignable) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int W = 1);\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module top;\n"
      "  m #(.P(5)) u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' has no parameter 'P'", 5, "23.10.2.2"));
}

uint32_t BodyTypeParamVarWidth(std::string_view items,
                               std::string_view assignment, ElabFixture& f) {
  auto* design = ElaborateBodyParamInstance(items, assignment, f);
  const RtlirVariable* x =
      design == nullptr ? nullptr : FindVar(design, "m", "x");
  return x == nullptr ? 0 : x->width;
}

TEST(BodyParameterAssignment, NamedAssignmentSetsABodyTypeParameter) {
  ElabFixture f;
  EXPECT_EQ(BodyTypeParamVarWidth("  parameter type T = int;\n  T x;\n",
                                  ".T(logic [7:0])", f),
            8u);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment, OrderedAssignmentSetsABodyTypeParameter) {
  ElabFixture f;
  EXPECT_EQ(BodyTypeParamVarWidth("  parameter type T = int;\n  T x;\n",
                                  "logic [7:0]", f),
            8u);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment, UnnamedBodyTypeParameterKeepsItsDefault) {
  ElabFixture f;
  EXPECT_EQ(BodyTypeParamVarWidth(
                "  parameter P = 1;\n  parameter type T = int;\n  T x;\n",
                ".P(5)", f),
            32u);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment, BodyTypeParameterAssignedAValueIsRejected) {
  ElabFixture f;
  BodyTypeParamVarWidth("  parameter type T = int;\n  T x;\n", ".T(3 + 4)", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter value assignment for type parameter "
                            "'T' of 'm' does not name a type",
                            6, "23.10.2"));
}

TEST(BodyParameterAssignment,
     BodyTypeParameterUnderAParameterPortListIsNotAssignable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #();\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  m #(.T(logic [7:0])) u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' has no parameter 'T'", 6, "23.10.2.2"));
  ASSERT_NE(design, nullptr);
  const RtlirVariable* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

int64_t ParamUnderConfig(const std::string& src, std::string_view name,
                         ElabFixture& f) {
  uint32_t fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  CompilationUnit* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  RtlirDesign* design = elab.Elaborate(cu->configs.front());
  f.has_errors = f.diag.HasErrors();
  return design == nullptr ? -1 : ParamValue(design, name);
}

TEST(BodyParameterAssignment, ConfigurationUseClauseReachesABodyParameter) {
  ElabFixture f;
  EXPECT_EQ(ParamUnderConfig("module m; parameter W = 32; localparam int Q = W;"
                             " endmodule\n"
                             "module top; m u(); endmodule\n"
                             "config cfg; design top; instance top.u use "
                             "#(.W(48)); endconfig\n",
                             "Q", f),
            48);
  EXPECT_FALSE(f.has_errors);
}

RtlirDesign* ElaborateChildrenUnderTop(std::string_view top_items,
                                       ElabFixture& f) {
  std::string src =
      "module c;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module d #(parameter W = 1);\n"
      "endmodule\n"
      "module top;\n";
  src += top_items;
  src += "endmodule\n";
  return ElaborateSrc(src, f, "top");
}

int64_t ChildParamUnderTop(RtlirDesign* design, std::string_view inst_name,
                           std::string_view name) {
  if (design == nullptr) return -1;
  for (const auto& child : design->top_modules[0]->children) {
    if (child.inst_name != inst_name || child.resolved == nullptr) continue;
    for (const auto& p : child.resolved->params) {
      if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
    }
  }
  return -1;
}

int64_t ConditionalBlockChildP(std::string_view inst, ElabFixture& f) {
  std::string items = "  if (1) begin : g\n    ";
  items += inst;
  items += "\n  end\n";
  return ChildParamUnderTop(ElaborateChildrenUnderTop(items, f), "g_u", "P");
}

TEST(BodyParameterAssignment,
     NamedAssignmentReachesABodyParameterUnderAConditionalGenerateBlock) {
  ElabFixture f;
  EXPECT_EQ(ConditionalBlockChildP("c #(.P(5)) u();", f), 5);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment,
     OrderedAssignmentReachesABodyParameterUnderAConditionalGenerateBlock) {
  ElabFixture f;
  EXPECT_EQ(ConditionalBlockChildP("c #(5) u();", f), 5);
  EXPECT_FALSE(f.has_errors);
}

void ExpectEachLoopInstancesP(std::string_view inst, int64_t value) {
  std::string items = "  for (genvar i = 0; i < 2; i++) begin : g\n    ";
  items += inst;
  items += "\n  end\n";
  ElabFixture f;
  RtlirDesign* design = ElaborateChildrenUnderTop(items, f);
  EXPECT_EQ(ChildParamUnderTop(design, "g_0_u", "P"), value);
  EXPECT_EQ(ChildParamUnderTop(design, "g_1_u", "P"), value);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterAssignment,
     NamedAssignmentReachesABodyParameterInEachLoopGenerateInstance) {
  ExpectEachLoopInstancesP("c #(.P(5)) u();", 5);
}

TEST(BodyParameterAssignment,
     OrderedAssignmentReachesABodyParameterInEachLoopGenerateInstance) {
  ExpectEachLoopInstancesP("c #(5) u();", 5);
}

TEST(BodyParameterAssignment,
     PortListParameterUnderAConditionalGenerateBlockTakesTheAssignment) {
  ElabFixture f;
  RtlirDesign* design = ElaborateChildrenUnderTop(
      "  if (1) begin : g\n    d #(.W(8)) v();\n  end\n", f);
  EXPECT_EQ(ChildParamUnderTop(design, "g_v", "W"), 8);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
