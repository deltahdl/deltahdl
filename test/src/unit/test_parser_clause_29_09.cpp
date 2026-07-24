#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §29.9 "Mixing level-sensitive and edge-sensitive descriptions". The clause's
// governing permission is that a single UDP state table may contain both
// level-sensitive rows (every input field is a level symbol) and edge-sensitive
// rows (one input field names a transition). The parser satisfies this by
// applying no per-table homogeneity restriction: its row validation (§29.6's
// at-most-one-edge-per-row rule, etc.) is per row, so a table freely combining
// the two kinds is accepted and both kinds survive into the produced AST.
//
// This is a parser-stage observation: build the primitive from real source and
// confirm (a) it parses with no diagnostics and (b) the resulting table holds
// at least one edge row AND at least one level row -- i.e. the mix was admitted
// rather than rejected or collapsed. The runtime resolution of a mixed table
// (edge cases first, level-sensitive case dominates on conflict) is observed in
// test_simulator_clause_29_09.cpp against the production evaluator.

// Mirrors src/parser/parser_udp.cpp's edge-symbol classification. A
// parenthesized transition is stored in the AST as the sentinel input '\x01'.
bool RowIsEdge(const UdpTableRow& row) {
  for (char c : row.inputs) {
    if (c == 'r' || c == 'R' || c == 'f' || c == 'F') return true;
    if (c == 'p' || c == 'P' || c == 'n' || c == 'N') return true;
    if (c == '*' || c == '\x01') return true;
  }
  return false;
}

// The clause's own worked example: a JK flip-flop whose preset/clear logic is
// level-sensitive while the normal clocking is edge-sensitive, all in one
// table. Columns are written one symbol per field (the LRM's grouped "jk"/"pc"
// notation is purely visual); input order after q is clock, j, k, preset,
// clear. Active-low preset/clear: pc == 01 presets, pc == 10 clears.
constexpr const char* kJkEdgeFf =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "  // clock j k preset clear : state : next\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic (level-sensitive)\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic (level-sensitive)\n"
    "    r 1 1 1 1 : 0 : 1 ;   // toggle on rising clock (edge-sensitive)\n"
    "    r 1 1 1 1 : 1 : 0 ;\n"
    "    f ? ? ? ? : ? : - ;   // ignore falling clock edge\n"
    "    b * ? ? ? : ? : - ;   // ignore j change on steady clock\n"
    "  endtable\n"
    "endprimitive\n";

TEST(MixedUdpTableParsing, MixedTableAcceptedWithBothRowKinds) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const UdpDecl& udp = *r.cu->udps[0];
  EXPECT_TRUE(udp.is_sequential);

  int edge_rows = 0;
  int level_rows = 0;
  for (const auto& row : udp.table) {
    if (RowIsEdge(row))
      ++edge_rows;
    else
      ++level_rows;
  }

  // The mix is what §29.9 permits: neither kind was dropped or rejected.
  EXPECT_GT(edge_rows, 0);
  EXPECT_GT(level_rows, 0);
  EXPECT_EQ(edge_rows + level_rows, static_cast<int>(udp.table.size()));
}

// §29.9's permission covers every edge form §29.6 admits, including a
// parenthesized transition. A table mixing a parenthesized-edge row (01) with a
// pure level row must be accepted, and both kinds must survive into the AST --
// the parenthesized transition is stored as the sentinel input '\x01', which
// RowIsEdge recognizes. Distinct parser input form from the letter/`*` edges
// exercised above.
TEST(MixedUdpTableParsing, ParenthesizedEdgeRowMixesWithLevelRow) {
  constexpr const char* kSrc =
      "primitive paren_mix (q, clk, d);\n"
      "  output q; reg q;\n"
      "  input clk, d;\n"
      "  table\n"
      "    (01) ? : ? : 1 ;   // edge via parenthesized transition\n"
      "    ?    1 : ? : 0 ;   // level-sensitive\n"
      "  endtable\n"
      "endprimitive\n";
  auto r = Parse(kSrc);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const UdpDecl& udp = *r.cu->udps[0];
  ASSERT_EQ(udp.table.size(), 2u);
  EXPECT_TRUE(RowIsEdge(udp.table[0]));
  EXPECT_FALSE(RowIsEdge(udp.table[1]));
}

}  // namespace
