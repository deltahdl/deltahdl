#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

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

std::vector<SpecifyItem*> CollectSpecparamsInSpecify(ModuleDecl* mod) {
  std::vector<SpecifyItem*> out;
  auto* spec = FindSpecifyBlock(mod->items);
  if (spec == nullptr) return out;
  for (auto* it : spec->specify_items) {
    if (it->kind == SpecifyItemKind::kSpecparam) out.push_back(it);
  }
  return out;
}

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

TEST(PulseControlSpecparamParsing, PulseControlSpecparamModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  specparam PATHPULSE$ = (2, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

size_t ErrorCount(const std::vector<Diagnostic>& diags) {
  return static_cast<size_t>(std::count_if(
      diags.begin(), diags.end(),
      [](const Diagnostic& d) { return d.severity == DiagSeverity::kError; }));
}

TEST(PulseControlSpecparamParsing, TerminalCannotBeBitOrPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$a[0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a PATHPULSE$ specparam names each terminal whole, "
                            "without selecting a bit or a part of it",
                            3, "30.7.1"));
  EXPECT_EQ(ErrorCount(r.diags), 1U);
}

TEST(PulseControlSpecparamParsing, TerminalCannotBePartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$a[1:0]$b = (1, 3);\n"
      "    specparam PATHPULSE$a$b[1] = (2);\n"
      "    specparam PATHPULSE$a$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a PATHPULSE$ specparam names each terminal whole, "
                            "without selecting a bit or a part of it",
                            3, "30.7.1"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a PATHPULSE$ specparam names each terminal whole, "
                            "without selecting a bit or a part of it",
                            4, "30.7.1"));
  EXPECT_EQ(ErrorCount(r.diags), 2U);
}

TEST(PulseControlSpecparamParsing,
     StandardExampleUnparenthesizedLimitIsReported) {
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
  EXPECT_TRUE(ReportedError(
      r.diags, "a PATHPULSE$ specparam's limits are written in parentheses", 10,
      "A.2.4"));
  EXPECT_EQ(ErrorCount(r.diags), 1U);
  auto specparams = CollectSpecparamsInSpecify(r.cu->modules[0]);
  ASSERT_EQ(specparams.size(), 3U);
  EXPECT_TRUE(specparams[0]->is_pathpulse);
  EXPECT_TRUE(specparams[1]->is_pathpulse);
  EXPECT_TRUE(specparams[2]->is_pathpulse);
  EXPECT_NE(specparams[2]->pathpulse_reject, nullptr);
  EXPECT_EQ(specparams[2]->pathpulse_error, nullptr);
}

TEST(PulseControlSpecparamParsing, PathSpecificBareLimitIsReported) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$q = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a PATHPULSE$ specparam's limits are written in parentheses", 3,
      "A.2.4"));
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->pathpulse_input, "clk");
  EXPECT_EQ(item->pathpulse_output, "q");
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_EQ(item->pathpulse_error, nullptr);
}

}  // namespace
