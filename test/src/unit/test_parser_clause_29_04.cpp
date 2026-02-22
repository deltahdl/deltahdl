// Tests for §29.4 — Sequential UDP definition

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static void VerifyUdpRowInputs(const UdpTableRow &row,
                               const std::string &expected) {
  ASSERT_EQ(row.inputs.size(), expected.size());
  for (size_t j = 0; j < expected.size(); ++j) {
    EXPECT_EQ(row.inputs[j], expected[j]);
  }
}

struct SeqUdpRow {
  std::string inputs;
  char state;
  char output;
};

static void VerifySeqUdpTable(const UdpDecl *udp, const SeqUdpRow expected[],
                              size_t count) {
  ASSERT_EQ(udp->table.size(), count);
  for (size_t i = 0; i < count; ++i) {
    VerifyUdpRowInputs(udp->table[i], expected[i].inputs);
    EXPECT_EQ(udp->table[i].current_state, expected[i].state);
    EXPECT_EQ(udp->table[i].output, expected[i].output);
  }
}

TEST(ParserSection29, SequentialUdp) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto *udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  SeqUdpRow expected[] = {{"0r", '?', '0'}, {"1r", '?', '1'}};
  VerifySeqUdpTable(udp, expected, std::size(expected));
}
