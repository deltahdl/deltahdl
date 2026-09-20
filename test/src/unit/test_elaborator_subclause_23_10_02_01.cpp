#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
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
  // The report states the allowed count, so it also says the localparam was
  // left out of the ordered list: two values are allowed, not three.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many positional parameter overrides for "
                            "module 'child': 3 provided, 2 allowed",
                            6, "23.10.2.1"));
}

// §23.10.2.1: an ordered override value is a constant expression evaluated in
// the instantiating scope. Building it from a value parameter of the parent
// (§6.20.2) instead of a literal drives the constant-evaluation scope-lookup
// path, while the same positional declaration-order binding rule applies.
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

// Same ordered-binding rule, but the override value is produced by a localparam
// of the parent (§6.20.4). A localparam is a valid constant source for the
// override even though a localparam cannot itself be overridden.
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

// §23.10.2.1 lets the ordered list assign values *or types* by position. A type
// parameter (§6.20.3) sits at position 0 here, so the ordered type argument
// overrides it; the effect is observed through the width of a variable declared
// with that type in the resolved child (byte default 8 -> shortint override
// 16).
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

// A module m declared with no parameter port list, its parameters written
// among its items as §23.10.2's own vdff is (printed page 766), with `items`
// as those items, instantiated once in top with `assignment` as the
// instance's parameter value assignment; answers m's parameter `name`.
int64_t BodyParamUnder(std::string_view items, std::string_view assignment,
                       std::string_view name, ElabFixture& f) {
  std::string src = "module m;\n";
  src += items;
  src += "endmodule\nmodule top;\n  m #(";
  src += assignment;
  src += ") u();\nendmodule\n";
  auto* design = ElaborateSrc(src, f, "top");
  return design == nullptr ? -1 : ParamValue(design, name);
}

// §23.10 (printed page 763) with §6.20.1 (printed 125): a module written with
// no parameter port list declares its parameters as module items, and
// §23.10.2 (printed 766) has an instance's parameter value assignment
// override the parameters of the instantiated module wherever they are
// declared. The assignment reached the parameter port list alone, so `m
// #(.P(5)) u()` kept P at 1 and Q, set from P, with it.
TEST(BodyParameterAssignment, NamedAssignmentReachesAParameterAmongTheItems) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  localparam int Q = P;\n",
                           ".P(5)", "Q", f),
            5);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.2.1 (printed page 766): the ordered list follows the order the
// parameters are declared in within the module, and a module with no
// parameter port list declares them among its items. `m #(5) u()` was
// refused as one value too many for a list of none.
TEST(BodyParameterAssignment, OrderedAssignmentReachesAParameterAmongTheItems) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  localparam int Q = P;\n", "5",
                           "Q", f),
            5);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.2.1's own vdff takes `#(10,15)` for `parameter size = 1, delay = 1;`
// (printed page 766): the first value binds to the first parameter declared
// and the second to the second, so A is 3 and B is 4 and Q reads 34; 43 would
// say the two were bound in the other order, and 12 that neither was.
TEST(BodyParameterAssignment,
     OrderedValuesBindToBodyParametersInDeclarationOrder) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter A = 1;\n  parameter B = 2;\n"
                           "  localparam int Q = A * 10 + B;\n",
                           "3, 4", "Q", f),
            34);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.2 (printed page 766): a parameter whose value depends on a second
// parameter takes the second's new value when the second is redefined
// (§23.10.3), and a body parameter written in terms of an earlier one is
// folded with the earlier one's overridden value in scope: D reads 10 and not
// the 2 of the declaration's own P.
TEST(BodyParameterAssignment, DependentBodyParameterIsRefoldedWithTheOverride) {
  ElabFixture f;
  EXPECT_EQ(BodyParamUnder("  parameter P = 1;\n  parameter D = P * 2;\n",
                           ".P(5)", "D", f),
            10);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 (printed page 126): a parameter with a range specification keeps the
// range of its declaration and an override value is converted to it, and the
// range is folded with the earlier parameters in scope, TOP's overridden
// value among them: `.TOP(7)` makes `logic [TOP:0] P` eight bits, so
// `.P(16'hABCD)` is cut to 0xCD, which Q reads, and $bits(P) is 8. The same
// declaration in a parameter port list is pinned by 79ea8c499 in
// test_elaborator_subclause_23_10_02_02.cpp.
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

// §6.20.4 (printed page 128): a local parameter cannot be modified by an
// instance parameter value assignment, so a localparam among the items is
// not one of the parameters a named assignment may name, and the report is
// the one a name the module does not declare draws (§23.10.2.2).
TEST(BodyParameterAssignment, NamedAssignmentToABodyLocalparamIsRejected) {
  ElabFixture f;
  BodyParamUnder("  localparam int L = 1;\n", ".L(5)", "L", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' has no parameter 'L'", 5, "23.10.2.2"));
}

// §6.20.1 (printed pages 125-126): where a design element has a parameter
// port list, even an empty one, `parameter` in a declaration among its items
// is a synonym for `localparam`, so the assignment cannot name it (§6.20.4).
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

// §33.4.3: a configuration's `instance <path> use #(.W(48))` overrides the
// named parameter of the configured instance, and every example module of
// the clause declares that parameter among its items (Examples 2, 3 and 8,
// printed pages 940-943). The configuration's assignments are installed for
// the module's items as an instantiation's are, so W is 48 and Q, set from
// W, reads it; the module default, 32, was printed before. `src` is
// elaborated through its one configuration, since ElaborateSrc elaborates a
// named top and applies none.
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

}  // namespace
