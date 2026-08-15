#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConfigDesignStatement, ZeroDesignStatementsRejected) {
  auto r = Parse(
      "config c;\n"
      "endconfig\n");
  // The report stands at the config_declaration, which is what lacks the
  // statement, so it is on line 1 rather than on the 'endconfig'.
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
  EXPECT_EQ(cells[0].library, "work");
  EXPECT_EQ(cells[0].cell, "top_a");
  EXPECT_EQ(cells[1].library, "work");
  EXPECT_EQ(cells[1].cell, "top_b");
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

TEST(ConfigDesignStatement, RuleBeforeDesignRejected) {
  auto r = Parse(
      "config c;\n"
      "  default liblist work;\n"
      "  design work.top;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'design' statement in config", 2,
                            "33.4.1.1"));
}

TEST(ConfigDesignStatement, MultipleBareTopModulesInOneDesignStatement) {
  // §33.4.1.1: several top-level modules may be listed in one design statement,
  // and each may be named without a library qualifier. Both bare cell names are
  // captured with an empty library for later resolution -- a different input
  // form than the library-qualified multi-cell list.
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

// §33.4.1.1 writes each entry of a design statement as
// `[ library_identifier . ] cell_identifier`, so the position the parser keeps
// for an entry is the cell_identifier's under both spellings. A report about a
// cell no library holds is about the cell, and a configuration naming several
// cells needs the position to say which of them a report is about.
//
// The source puts every identifier off line 1 and off column 1, and puts the
// qualified entry's library_identifier in a different column from its
// cell_identifier, so a parser recording nothing, recording the statement's
// position, or recording the library_identifier's each fails a claim below.
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

// §33.4.1.1 terminates the design statement with a ';'. A cell list left
// without one is rejected at the token standing where the ';' belongs, and the
// report names §33.4.1.1 rather than the token it wanted. The case lives in
// this file rather than in test_parser_subclause_33_04_01.cpp because §33.4.1.1
// is the subclause that states the statement, and each file holds the cases for
// the subclause it is named for.
TEST(ConfigDesignStatement, MalformedDesignStatementNames33_4_1_1) {
  auto r = Parse(
      "config cfg;\n"
      "  design top\n"
      "endconfig\n");
  ASSERT_FALSE(r.diags.empty());
  EXPECT_EQ(r.diags.front().subclause, "33.4.1.1");
  EXPECT_EQ(r.diags.front().loc.line, 3u);
  EXPECT_EQ(r.diags.front().loc.column, 1u);
}

}  // namespace
