#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"

using namespace delta;

namespace {

TEST(CellClauseNotation, LibraryQualifiedNameSplitsIntoLibraryAndCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  cell gateLib.adder liblist gateLib;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& rules = r.cu->configs[0]->rules;
  ASSERT_EQ(rules.size(), 1u);
  EXPECT_EQ(rules[0]->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rules[0]->cell_lib, "gateLib");
  EXPECT_EQ(rules[0]->cell_name, "adder");
}

TEST(CellClauseNotation, BareNameIsTheCellAndNamesNoLibrary) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  cell adder liblist gateLib;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& rules = r.cu->configs[0]->rules;
  ASSERT_EQ(rules.size(), 1u);
  EXPECT_TRUE(rules[0]->cell_lib.empty());
  EXPECT_EQ(rules[0]->cell_name, "adder");
}

TEST(CellClauseNotation, QualifierWithoutCellIdentifierRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  cell gateLib. liblist gateLib;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got 'liblist'", 3,
                            "33.4.1.4"));
}

TEST(CellClauseNotation, TwiceQualifiedNameRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  cell gateLib.inner.adder liblist gateLib;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cell selection requires a 'liblist' or 'use' clause", 3,
      "33.4.1"));
}

TEST(CellClauseNotation, NameWithoutCellKeywordRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  gateLib.adder liblist gateLib;\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 3, "33.4.1"));
}

TEST(CellClauseNotation, EscapedIdentifiersAdmittedForLibraryAndCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design rtlLib.top;\n"
      "  cell \\gateLib .\\adder$1 liblist gateLib;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& rules = r.cu->configs[0]->rules;
  ASSERT_EQ(rules.size(), 1u);
  EXPECT_EQ(rules[0]->cell_lib, "gateLib");
  EXPECT_EQ(rules[0]->cell_name, "adder$1");
}

}  // namespace
