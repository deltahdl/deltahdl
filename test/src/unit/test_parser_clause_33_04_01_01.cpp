#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConfigDesignStatement, ZeroDesignStatementsRejected) {
  auto r = Parse(
      "config c;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigDesignStatement, DuplicateDesignStatementsRejected) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  design work.other;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigDesignStatement, MultipleTopModulesInOneDesignStatement) {
  // §33.4.1.1: multiple top-level modules may be listed in a single design
  // statement.
  auto r = Parse(
      "config c;\n"
      "  design work.top_a work.top_b;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_EQ(cells[0].first, "work");
  EXPECT_EQ(cells[0].second, "top_a");
  EXPECT_EQ(cells[1].first, "work");
  EXPECT_EQ(cells[1].second, "top_b");
}

TEST(ConfigDesignStatement, BareCellNameStoredWithoutLibrary) {
  // §33.4.1.1: a design statement may name a cell without a library qualifier.
  // The parser captures the cell name and leaves the library empty for later
  // resolution.
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 1u);
  EXPECT_TRUE(cells[0].first.empty());
  EXPECT_EQ(cells[0].second, "top");
}

TEST(ConfigDesignStatement, DesignBeforeRulesAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigDesignStatement, RuleBeforeDesignRejected) {
  auto r = Parse(
      "config c;\n"
      "  default liblist work;\n"
      "  design work.top;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
