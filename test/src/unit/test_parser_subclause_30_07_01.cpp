#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

SpecifyItem* FindPathpulseInSpecify(ModuleDecl* mod) {
  auto* spec = FindSpecifyBlock(mod->items);
  if (spec == nullptr) return nullptr;
  for (auto* it : spec->specify_items) {
    if (it->kind == SpecifyItemKind::kSpecparam && it->is_pathpulse) return it;
  }
  return nullptr;
}

// Every specparam item the specify block of `mod` declares, in declaration
// order. §30.7.1's worked example writes its three PATHPULSE$ specparams as one
// comma-separated declaration, so a case about that declaration has to read the
// whole list rather than the first item FindPathpulseInSpecify answers with.
std::vector<SpecifyItem*> CollectSpecparamsInSpecify(ModuleDecl* mod) {
  std::vector<SpecifyItem*> out;
  auto* spec = FindSpecifyBlock(mod->items);
  if (spec == nullptr) return out;
  for (auto* it : spec->specify_items) {
    if (it->kind == SpecifyItemKind::kSpecparam) out.push_back(it);
  }
  return out;
}

// Syntax 30-7 first alternative (PATHPULSE$ = ( reject )): a lone reject limit
// produces a module-wide pathpulse specparam with no error limit.
TEST(PulseControlSpecparamParsing, PathpulseRejectOnlyExtraction) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_pathpulse);
  EXPECT_TRUE(item->pathpulse_input.empty());
  EXPECT_TRUE(item->pathpulse_output.empty());
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_EQ(item->pathpulse_error, nullptr);
}

// Syntax 30-7 second alternative
// (PATHPULSE$ input $ output = ( ... )): the input and output terminal
// descriptors are captured for a path-specific specparam.
TEST(PulseControlSpecparamParsing, PathpulseExtractsInputOutputTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$q = (3, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_pathpulse);
  EXPECT_EQ(item->pathpulse_input, "clk");
  EXPECT_EQ(item->pathpulse_output, "q");
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_NE(item->pathpulse_error, nullptr);
}

// limit_value ::= constant_mintypmax_expression: each limit may be a full
// min:typ:max triple.
TEST(PulseControlSpecparamParsing, PathpulseMintypmaxExpressionPreserved) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->pathpulse_reject, nullptr);
  ASSERT_NE(item->pathpulse_error, nullptr);
  EXPECT_EQ(item->pathpulse_reject->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->pathpulse_error->kind, ExprKind::kMinTypMax);
}

// limit_value ::= constant_mintypmax_expression: a limit need not be a bare
// literal. A constant expression built from an identifier operand (e.g. a
// specparam per 11.2.1) and an operator is accepted and preserved as the
// reject-limit expression.
TEST(PulseControlSpecparamParsing, PathpulseConstantExpressionLimit) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam lim = 5;\n"
      "    specparam PATHPULSE$ = (lim + 1);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->pathpulse_reject, nullptr);
  EXPECT_EQ(item->pathpulse_reject->kind, ExprKind::kBinary);
  EXPECT_EQ(item->pathpulse_error, nullptr);
}

// The PATHPULSE$ specparam form is also accepted in a module-level specparam
// declaration, exercising the separate specparam-declaration parse path.
TEST(PulseControlSpecparamParsing, PulseControlSpecparamModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  specparam PATHPULSE$ = (2, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §30.7.1: the module path input and output terminals may not be a bit-select
// or part-select of a vector. Such a terminal cannot form a PATHPULSE$
// identifier (the brackets terminate the identifier), so the declaration is
// rejected.
TEST(PulseControlSpecparamParsing, TerminalCannotBeBitOrPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$a[0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  // The '[' ends the identifier, so what the parser reports is the specparam
  // name not being followed by '='; §6.20.5 owns that, not §30.7.1.
  EXPECT_TRUE(ReportedError(r.diags, "expected '=', got '['", 3, "6.20.5"));
}

// The other rejected select form: a part-select terminal. Like the bit-select
// case, the `[` closes the identifier, so a range select cannot form part of a
// PATHPULSE$ terminal name and the declaration is rejected.
TEST(PulseControlSpecparamParsing, TerminalCannotBePartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$a[1:0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  // The '[' ends the identifier, so what the parser reports is the specparam
  // name not being followed by '='; §6.20.5 owns that, not §30.7.1.
  EXPECT_TRUE(ReportedError(r.diags, "expected '=', got '['", 3, "6.20.5"));
}

// §30.7.1's own worked example, printed on page 888 and reproduced here
// verbatim -- the blank line, the `(2,9)` written without a space, and above
// all the final `PATHPULSE$ = 3;` written with no parentheses at all. Syntax
// 30-7 and A.2.4 both parenthesize the limit list, so the standard's grammar
// and its example disagree and the example is what a user copies. Issue #3384
// is that this source was rejected. Every other case in this file writes the
// non-path-specific limit as `= (3)`, so this is the one that decides it.
//
// The delays 12, 10 and 4 and the limits 2, 9 and 3 are the example's own
// numbers, and no two of them coincide, so a value read off the wrong
// declaration is caught. The 0 in `(0,4)` is the exception: nothing here
// asserts on it, because an unset limit and a limit of 0 read the same.
TEST(PulseControlSpecparamParsing, StandardExampleUnparenthesizedLimitParses) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    (clr, pre *> q) = 4;\n"
      "\n"
      "  specparam\n"
      "      PATHPULSE$clk$q = (2,9),\n"
      "      PATHPULSE$clr$q = (0,4),\n"
      "      PATHPULSE$ = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto specparams = CollectSpecparamsInSpecify(r.cu->modules[0]);
  ASSERT_EQ(specparams.size(), 3U);
  EXPECT_TRUE(specparams[0]->is_pathpulse);
  EXPECT_TRUE(specparams[1]->is_pathpulse);
  EXPECT_TRUE(specparams[2]->is_pathpulse);
  // The unparenthesized limit is a reject limit alone. §30.7.1: "If only the
  // reject limit value is specified, it shall apply to both the reject limit
  // and the error limit", which the null error limit is what carries.
  EXPECT_NE(specparams[2]->pathpulse_reject, nullptr);
  EXPECT_EQ(specparams[2]->pathpulse_error, nullptr);
}

// Syntax 30-7 gives both alternatives the same parenthesized limit list, so
// dropping the parentheses from the path-specific alternative is the same
// disagreement with §30.7.1's example as dropping them from the
// non-path-specific one, and a fix reaching only the second alternative would
// leave this source rejected. 3 is the one limit written in this source, so no
// other value can stand in for it.
TEST(PulseControlSpecparamParsing, PathSpecificLimitNeedsNoParentheses) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$q = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->pathpulse_input, "clk");
  EXPECT_EQ(item->pathpulse_output, "q");
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_EQ(item->pathpulse_error, nullptr);
}

}  // namespace
