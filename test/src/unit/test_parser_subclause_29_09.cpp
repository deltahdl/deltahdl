#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

bool RowIsEdge(const UdpTableRow& row) {
  for (char c : row.inputs) {
    if (c == 'r' || c == 'R' || c == 'f' || c == 'F') return true;
    if (c == 'p' || c == 'P' || c == 'n' || c == 'N') return true;
    if (c == '*' || c == '\x01') return true;
  }
  return false;
}

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

  EXPECT_GT(edge_rows, 0);
  EXPECT_GT(level_rows, 0);
  EXPECT_EQ(edge_rows + level_rows, static_cast<int>(udp.table.size()));
}

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
