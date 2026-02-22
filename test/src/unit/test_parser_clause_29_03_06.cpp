// Tests for LRM section 29.3.6 -- UDP state table entries

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult29 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult29 Parse(const std::string &src) {
  ParseResult29 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =============================================================================
// LRM section 29.3.6 -- UDP state table entries: symbol summary
// =============================================================================

// --- Combinational UDP table symbols ---

TEST(ParserSection29, TableSymbol0And1) {
  auto r = Parse("primitive and_gate(output out, input a, b);\n"
                 "  table\n"
                 "    0 0 : 0;\n"
                 "    0 1 : 0;\n"
                 "    1 0 : 0;\n"
                 "    1 1 : 1;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto *udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4);
  // Verify first row: inputs '0','0', output '0'
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  // Verify last row: inputs '1','1', output '1'
  EXPECT_EQ(udp->table[3].inputs[0], '1');
  EXPECT_EQ(udp->table[3].inputs[1], '1');
  EXPECT_EQ(udp->table[3].output, '1');
}

TEST(ParserSection29, TableSymbolQuestionMark) {
  auto r = Parse("primitive buf_udp(output out, input in);\n"
                 "  table\n"
                 "    0 : 0;\n"
                 "    1 : 1;\n"
                 "    ? : x;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->udps[0]->table.size(), 3);
  // Third row uses ? as input
  EXPECT_EQ(r.cu->udps[0]->table[2].inputs[0], '?');
  EXPECT_EQ(r.cu->udps[0]->table[2].output, 'x');
}

TEST(ParserSection29, TableSymbolX) {
  auto r = Parse("primitive xor_udp(output out, input a, b);\n"
                 "  table\n"
                 "    0 0 : 0;\n"
                 "    0 1 : 1;\n"
                 "    1 0 : 1;\n"
                 "    1 1 : 0;\n"
                 "    x ? : x;\n"
                 "    ? x : x;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 6);
  // Row with x input
  EXPECT_EQ(udp->table[4].inputs[0], 'x');
  EXPECT_EQ(udp->table[4].inputs[1], '?');
  EXPECT_EQ(udp->table[4].output, 'x');
}

TEST(ParserSection29, TableSymbolB) {
  auto r = Parse("primitive or_udp(output out, input a, b);\n"
                 "  table\n"
                 "    b 0 : 0;\n"
                 "    0 b : 0;\n"
                 "    1 ? : 1;\n"
                 "    ? 1 : 1;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 4);
  EXPECT_EQ(udp->table[0].inputs[0], 'b');
  EXPECT_EQ(udp->table[1].inputs[1], 'b');
}

// --- Sequential UDP table symbols ---

TEST(ParserSection29, TableSymbolDashNoChange) {
  auto r = Parse("primitive latch(output reg q, input d, en);\n"
                 "  table\n"
                 "    0 1 : ? : 0;\n"
                 "    1 1 : ? : 1;\n"
                 "    ? 0 : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 3);
  // Third row: no-change output
  EXPECT_EQ(udp->table[2].output, '-');
  // Current state field should be '?'
  EXPECT_EQ(udp->table[2].current_state, '?');
}

TEST(ParserSection29, TableEdgeSymbolsRAndF) {
  auto r = Parse("primitive dff(output reg q, input d, clk);\n"
                 "  table\n"
                 "    0 r : ? : 0;\n"
                 "    1 r : ? : 1;\n"
                 "    ? f : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[1].inputs[1], 'r');
  EXPECT_EQ(udp->table[2].inputs[1], 'f');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(ParserSection29, TableEdgeSymbolStar) {
  auto r = Parse("primitive any_change(output reg q, input d, clk);\n"
                 "  table\n"
                 "    0 r : ? : 0;\n"
                 "    1 r : ? : 1;\n"
                 "    * ? : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);
  EXPECT_EQ(udp->table[2].inputs[0], '*');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(ParserSection29, TableEdgeSymbolsPAndN) {
  EXPECT_TRUE(ParseOk("primitive pos_neg(output reg q, input d, clk);\n"
                      "  table\n"
                      "    0 p : ? : 0;\n"
                      "    1 p : ? : 1;\n"
                      "    ? n : ? : -;\n"
                      "  endtable\n"
                      "endprimitive\n"));
}

TEST(ParserSection29, TableEdgeNotationParenthesized) {
  EXPECT_TRUE(ParseOk("primitive edge_udp(output reg q, input d, clk);\n"
                      "  table\n"
                      "    0 (01) : ? : 0;\n"
                      "    1 (01) : ? : 1;\n"
                      "    ? (10) : ? : -;\n"
                      "    ? (0x) : ? : -;\n"
                      "    ? (x1) : ? : -;\n"
                      "  endtable\n"
                      "endprimitive\n"));
}

TEST(ParserSection29, SequentialCurrentStateField) {
  auto r = Parse("primitive srff(output reg q, input s, r);\n"
                 "  table\n"
                 "    1 0 : 0 : 1;\n"
                 "    1 0 : 1 : 1;\n"
                 "    0 1 : ? : 0;\n"
                 "    0 0 : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4);
  // First row: current state '0', output '1'
  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');
  // Second row: current state '1', output '1'
  EXPECT_EQ(udp->table[1].current_state, '1');
  EXPECT_EQ(udp->table[1].output, '1');
  // Third row: current state '?'
  EXPECT_EQ(udp->table[2].current_state, '?');
  EXPECT_EQ(udp->table[2].output, '0');
  // Fourth row: no-change
  EXPECT_EQ(udp->table[3].current_state, '?');
  EXPECT_EQ(udp->table[3].output, '-');
}
