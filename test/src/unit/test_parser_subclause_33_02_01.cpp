// Tests for IEEE 1800-2023 §33.2.1 "Library notation" (Syntax 33-1). The
// subclause gives the symbolic notation that names a cell of a library:
//
//   cell_clause ::= cell [ library_identifier . ] cell_identifier
//
// Each test observes the parser applying that production. The rules the
// selected cell is then bound by belong to other subclauses and are not
// exercised here.
//
// The subclause also settles which design elements a library holds as cells.
// Nothing of that is visible at this stage -- a cell identifier is an
// identifier whatever kind of element declared it, so a source naming a
// primitive parses down the same path as one naming a module. That claim is
// observed where the kind actually decides something, in the elaborator file
// for this subclause.
#include "fixture_parser.h"

using namespace delta;

namespace {

// The library identifier is optional, so the notation names a cell either on
// its own or qualified by the library holding it. Distinct spellings for the
// library and the cell keep the two apart: a parser that stored the qualified
// form under one field would report the same text twice.
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

// With the optional library omitted, the one identifier written is the cell
// name and no library is recorded -- the notation then leaves the library to be
// searched for rather than naming it.
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

// The cell identifier is the one part of the production that is not optional,
// so a qualifier with nothing after the dot names no cell.
TEST(CellClauseNotation, QualifierWithoutCellIdentifierRejected) {
  EXPECT_FALSE(
      ParseOk("config cfg;\n"
              "  design rtlLib.top;\n"
              "  cell gateLib. liblist gateLib;\n"
              "endconfig\n"));
}

// The notation reaches exactly one level: a library holds cells, and a cell is
// a design element rather than a further collection, so there is no second
// qualifier to write.
TEST(CellClauseNotation, TwiceQualifiedNameRejected) {
  EXPECT_FALSE(
      ParseOk("config cfg;\n"
              "  design rtlLib.top;\n"
              "  cell gateLib.inner.adder liblist gateLib;\n"
              "endconfig\n"));
}

// The keyword is what introduces the notation; the name alone continues no
// production of the config grammar.
TEST(CellClauseNotation, NameWithoutCellKeywordRejected) {
  EXPECT_FALSE(
      ParseOk("config cfg;\n"
              "  design rtlLib.top;\n"
              "  gateLib.adder liblist gateLib;\n"
              "endconfig\n"));
}

// Both parts of the notation are identifiers, so either may be written in the
// escaped form -- which is how a cell whose name would otherwise collide with a
// keyword, or carries punctuation, is reachable at all. The leading backslash
// and the terminating white space delimit the name without belonging to it, so
// the parts recorded are the names themselves.
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
