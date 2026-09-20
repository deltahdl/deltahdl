#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

namespace {

// Config-elaborates `src` through its first configuration and returns the cell
// bound to the first child instance of the design's top module, so that
// configuration-applied parameter values can be inspected (§33.4.3).
RtlirModule* ConfigElabFirstChild(ElabFixture& f, const std::string& src) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  f.has_errors = f.diag.HasErrors();
  if (!design || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

int64_t ResolvedParam(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return p.resolved_value;
  }
  return -1;
}

TEST(ConfigLocalparamLiteral, NonLiteralLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 1 + 2;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  // The report stands at the localparam's own value on line 3, not at the
  // 'config' keyword on line 2: it is the expression that is not a literal.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' localparam 'X' is not assigned a "
                            "literal value",
                            3, "33.4.3"));
}

TEST(ConfigLocalparamLiteral, IdentifierLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = a;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' localparam 'X' is not assigned a "
                            "literal value",
                            3, "33.4.3"));
}

TEST(ConfigLocalparamLiteral, IntegerLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 8;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, StringLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam S = \"name\";\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// A real literal is as much a literal value as an integer or string, so a
// config localparam set directly to one is accepted (§33.4.3).
TEST(ConfigLocalparamLiteral, RealLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam R = 1.5;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// An unbased-unsized literal ('0/'1/'x/'z) is a literal value, so a config
// localparam set directly to one is accepted (§33.4.3).
TEST(ConfigLocalparamLiteral, UnbasedUnsizedLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam U = '1;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// A time literal (e.g. 5ns) is likewise a literal value and is accepted as a
// config localparam initializer (§33.4.3).
TEST(ConfigLocalparamLiteral, TimeLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam T = 5ns;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierIdentInExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "config 'c' override of parameter 'W' embeds a "
                    "hierarchical identifier inside a larger expression",
                    4, "33.4.3"));
}

// §33.4.1 admits any number of instance clauses in one config and §33.4.3 lets
// each carry its own overrides, so the report has to say which clause it is
// about. Two clauses are written on separate lines and only the second is
// illegal, because a config whose clauses share a line makes the clause's
// position and the config's position the same number and would pass whether
// the report moved or not.
TEST(ConfigParamOverride, ReportStandsAtTheOffendingUseClause) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(8));\n"
      "  instance top.a2 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  // Line 5 is the second clause, whose override is the illegal one. Line 2 is
  // the `config` keyword and line 4 the legal clause, so an assertion naming 5
  // fails if the report stands at either.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "config 'c' override of parameter 'W' embeds a "
                    "hierarchical identifier inside a larger expression",
                    5, "33.4.3"));
}

TEST(ConfigParamOverride, HierIdentAloneAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, NonHierIdentInExpressionAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingUnknownIdentifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses index "
                            "identifier 'i' that is neither a literal nor a "
                            "localparam of the config",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, IndexUsingLiteralAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingConfigLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam IDX = 0;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[IDX]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierRefThroughArrayOfInstancesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.arr[0].WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses a "
                            "hierarchical reference that traverses an array of "
                            "instances",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, UserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(my_func(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' calls a "
                            "user-defined function; only built-in constant "
                            "functions are permitted",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, SystemFunctionCallAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W($clog2(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// An override with empty parentheses requests a reset to the module default
// and is a legal override; the parameter-override validator must accept it
// rather than treating the absent expression as malformed (§33.4.3).
TEST(ConfigParamOverride, EmptyParamOverrideAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W());\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// An empty override list requests a reset of every parameter to its module
// default and is likewise a legal use clause (§33.4.3).
TEST(ConfigParamOverride, EmptyParamListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #();\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// The literal-or-config-localparam restriction on index expressions applies to
// every bound of a part-select, not only the first; an unknown identifier in
// the upper/lower bound of a range select is rejected (§33.4.3).
TEST(ConfigParamOverride, RangeSelectBoundNonLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2:i]));\n"
      "endconfig\n",
      f, "top");
  // The literal bound 2 draws no report, so naming 'i' says the upper bound was
  // the one checked.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses index "
                            "identifier 'i' that is neither a literal nor a "
                            "localparam of the config",
                            4, "33.4.3"));
}

// The prohibition on calling a user-defined function reaches a call buried
// inside a larger override expression, not only a call standing alone
// (§33.4.3).
TEST(ConfigParamOverride, NestedUserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(1 + my_func(2)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' calls a "
                            "user-defined function; only built-in constant "
                            "functions are permitted",
                            4, "33.4.3"));
}

// A configuration override applies the named value to the bound instance's
// parameter (§33.4.3).
TEST(ConfigParamApply, OverrideSetsInstanceParameter) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

// The override value may be a configuration localparam; it resolves against the
// config's own localparam scope and its literal value reaches the bound
// instance's parameter (§33.4.3).
TEST(ConfigParamApply, OverrideUsingConfigLocalparamValue) {
  ElabFixture f;
  auto* a1 =
      ConfigElabFirstChild(f,
                           "module adder #(parameter W = 8) (); endmodule\n"
                           "module top; adder a1(); endmodule\n"
                           "config c; localparam V = 24; design top;\n"
                           "  instance top.a1 use #(.W(V)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 24);
}

// The override value may name a parameter of the instance's parent; §33.4.3
// resolves parameter identifiers starting in that parent scope, so the parent's
// value is what the bound instance receives.
TEST(ConfigParamApply, OverrideUsingParentParameterValue) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; parameter P = 20; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(P)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 20);
}

// An override with empty parentheses returns just that parameter to its module
// default, discarding the value the instantiation supplied (§33.4.3).
TEST(ConfigParamApply, EmptyOverrideResetsParameterToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder #(.W(16)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(.W()); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
}

// An empty override list returns every parameter to its module default,
// discarding all values the instantiation supplied (§33.4.3).
TEST(ConfigParamApply, EmptyListResetsAllParametersToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8, parameter D = 4) (); endmodule\n"
      "module top; adder #(.W(16), .D(2)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
  EXPECT_EQ(ResolvedParam(a1, "D"), 4);
}

// A configuration override of a parameter takes precedence over a defparam
// targeting the same parameter at the same level of hierarchy (§33.4.3).
TEST(ConfigParamApply, OverrideTakesPrecedenceOverDefparam) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); defparam a1.W = 16; endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

// §33.4.3 (printed page 940) has a use clause's `#(.P(5))` assign a value to
// a parameter of the configured instance, and §6.20.4 (printed 128) puts a
// local parameter beyond every instance parameter value assignment. §6.20.1
// (printed 125-126) makes a `parameter` among the items of a module with a
// parameter port list, even an empty one, a synonym for `localparam`, so P
// here is one. The clause was applied and ignored in silence, P staying 2
// with nothing reported; the report stands on line 4, the clause's own line,
// and P keeps the value of its declaration. The wording is the one a defparam
// on a local parameter draws (§23.10.1's report), with the configuration as
// the actor.
TEST(ConfigParamApply, UseClauseNamingABodyParameterUnderAPortListIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c #(parameter W = 1); parameter P = 2; endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top;\n"
      "  instance top.u use #(.P(5));\n"
      "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "configuration cannot override a local parameter: "
                            "'P' of module 'c'",
                            4, "6.20.4"));
  EXPECT_EQ(ResolvedParam(u, "P"), 2);
}

// The same clause on a module declared with no parameter port list names a
// value parameter (§6.20.1), which §33.4.3's own examples override this way
// (printed pages 940-943), so it is applied and nothing is reported: P reads
// 5.
TEST(ConfigParamApply, UseClauseOnABodyParameterOfAModuleWithoutAPortList) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
}

// §33.4.3 (printed page 940): a parameter override from a configuration
// takes precedence over a defparam on the same parameter, and `use #()`
// returns every parameter of the instance to its module default (printed
// 941). P is declared among the items of a module with no parameter port
// list (§6.20.1, printed 125-126), so the instance's `.P(7)` is discarded and
// the defparam's 9 is refused: P reads 2. The `#()` locked the parameter port
// list's parameters alone, so the defparam made P 9.
TEST(ConfigParamApply, EmptyListLocksABodyParameterAgainstADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c #(.P(7)) u(); defparam u.P = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 2);
}

// The precedence is the named assignment's as well: `use #(.P(5))` on the
// same body parameter holds 5 against `defparam u.P = 9`.
TEST(ConfigParamApply, NamedUseClauseLocksABodyParameterAgainstADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c u(); defparam u.P = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
}

// §33.4.3 (printed page 940) gives the configuration precedence where both
// reference the same parameter, and in every other condition the defparam
// works as §23.10.1 defines it: a body parameter the use clause does not
// name is still the defparam's, so Q reads 9 beside the clause's P.
TEST(ConfigParamApply, UseClauseLeavesAnUnnamedBodyParameterToADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; parameter Q = 3; endmodule\n"
      "module top; c u(); defparam u.Q = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
  EXPECT_EQ(ResolvedParam(u, "Q"), 9);
}

// §33.4.3 (printed page 940) has the use clause's parameter value assignment
// name a parameter of the configured instance, by name alone, positional
// notation being refused; §23.10.2.2 (printed 767) is the rule for the name,
// which is the one the instantiated module specifies. A name no parameter of
// c bears passed AssignableConfigParams as none of its local parameters and
// was applied to nothing in silence, so `use #(.X(5), .P(7))` reported
// nothing. The report is the one `c #(.X(5)) u()` draws, on line 4, the
// clause's own line, and the clause's P still reads 7 beside it.
TEST(ConfigParamApply, UseClauseNamingNoParameterOfTheModuleIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(f,
                                 "module c; parameter P = 2; endmodule\n"
                                 "module top; c u(); endmodule\n"
                                 "config cfg; design top;\n"
                                 "  instance top.u use #(.X(5), .P(7));\n"
                                 "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'c' has no parameter 'X'", 4, "23.10.2.2"));
  EXPECT_EQ(ResolvedParam(u, "P"), 7);
}

// The same on a module with a parameter port list, whose parameters are the
// port list's alone (§6.20.1, printed pages 125-126): X is no parameter of
// c and is reported as above, W keeping its default. The known port-list
// parameter passes as OverrideSetsInstanceParameter above reads it.
TEST(ConfigParamApply, UseClauseNamingNoParameterOfAPortListIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c #(parameter W = 1); endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top; instance top.u use #(.X(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'c' has no parameter 'X'", 3, "23.10.2.2"));
  EXPECT_EQ(ResolvedParam(u, "W"), 1);
}

}  // namespace
