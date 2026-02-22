// Tests for §29.3 — Combinational UDP definition

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

struct CombUdpRow {
  std::string inputs;
  char output;
};

static void VerifyCombUdpTable(const UdpDecl *udp, const CombUdpRow expected[],
                               size_t count) {
  ASSERT_EQ(udp->table.size(), count);
  for (size_t i = 0; i < count; ++i) {
    VerifyUdpRowInputs(udp->table[i], expected[i].inputs);
    EXPECT_EQ(udp->table[i].output, expected[i].output);
  }
}

static void VerifyUdpInputNames(const UdpDecl *udp,
                                const std::string expected[], size_t count) {
  ASSERT_EQ(udp->input_names.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->input_names[i], expected[i]);
  }
}

TEST(ParserSection29, CombinationalUdp) {
  auto r = Parse("primitive mux(output out, input a, b, sel);\n"
                 "  table\n"
                 "    0 ? 0 : 0;\n"
                 "    1 ? 0 : 1;\n"
                 "    ? 0 1 : 0;\n"
                 "    ? 1 1 : 1;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto *udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "mux");
  EXPECT_EQ(udp->output_name, "out");
  EXPECT_FALSE(udp->is_sequential);
  std::string expected_inputs[] = {"a", "b", "sel"};
  VerifyUdpInputNames(udp, expected_inputs, std::size(expected_inputs));
  CombUdpRow expected_rows[] = {
      {"0?0", '0'}, {"1?0", '1'}, {"?01", '0'}, {"?11", '1'}};
  VerifyCombUdpTable(udp, expected_rows, std::size(expected_rows));
  EXPECT_EQ(udp->table[0].current_state, 0);
}

TEST(ParserSection29, UdpTableSpecialChars) {
  auto r = Parse("primitive edge_detect(output reg q, input d, clk);\n"
                 "  table\n"
                 "    ? f : ? : 1;\n"
                 "    ? p : ? : 0;\n"
                 "    * ? : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto *udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);

  struct Check {
    size_t row;
    size_t col;
    char val;
  };
  Check input_checks[] = {{0, 1, 'f'}, {1, 1, 'p'}, {2, 0, '*'}};
  for (const auto &c : input_checks) {
    EXPECT_EQ(udp->table[c.row].inputs[c.col], c.val);
  }
  EXPECT_EQ(udp->table[2].output, '-');
}
