#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConfigDesignStatement, ZeroDesignStatementsRejected) {
  auto r = Parse(
      "config c;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "config 'c' is missing a 'design' statement", 1, "33.4.1.1"));
}

TEST(ConfigDesignStatement, DuplicateDesignStatementsRejected) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  design work.other;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "duplicate 'design' statement in config 'c'", 3, "33.4.1.1"));
}

TEST(ConfigDesignStatement, MultipleTopModulesInOneDesignStatement) {
  auto r = Parse(
      "config c;\n"
      "  design work.top_a work.top_b;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_EQ(cells[0].library, "work");
  EXPECT_EQ(cells[0].cell, "top_a");
  EXPECT_EQ(cells[1].library, "work");
  EXPECT_EQ(cells[1].cell, "top_b");
}

TEST(ConfigDesignStatement, BareCellNameStoredWithoutLibrary) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 1u);
  EXPECT_TRUE(cells[0].library.empty());
  EXPECT_EQ(cells[0].cell, "top");
}

TEST(ConfigDesignStatement, DesignBeforeRulesAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigDesignStatement, RuleBeforeDesignRejectedOnce) {
  auto r = Parse(
      "config c;\n"
      "  default liblist work;\n"
      "  design work.top;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "config 'c' places its 'design' statement after a "
                            "config rule statement",
                            3, "33.4.1.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(ConfigDesignStatement, MultipleBareTopModulesInOneDesignStatement) {
  auto r = Parse(
      "config c;\n"
      "  design top_a top_b;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_TRUE(cells[0].library.empty());
  EXPECT_EQ(cells[0].cell, "top_a");
  EXPECT_TRUE(cells[1].library.empty());
  EXPECT_EQ(cells[1].cell, "top_b");
}

TEST(ConfigDesignStatement, CellPositionRecordedAtCellIdentifier) {
  auto r = Parse(
      "config c;\n"
      "  design top_a\n"
      "         lib.top_b;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_EQ(cells[0].cell, "top_a");
  EXPECT_EQ(cells[0].loc.line, 2u);
  EXPECT_EQ(cells[0].loc.column, 10u);
  EXPECT_EQ(cells[1].cell, "top_b");
  EXPECT_EQ(cells[1].loc.line, 3u);
  EXPECT_EQ(cells[1].loc.column, 14u);
}

TEST(ConfigDesignStatement, MalformedDesignStatementNames33_4_1_1) {
  auto r = Parse(
      "config cfg;\n"
      "  design top\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 3, "33.4.1.1"));
}

}  // namespace
