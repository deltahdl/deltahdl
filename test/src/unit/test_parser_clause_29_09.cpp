// Tests for §29.9 — Mixing level-sensitive and edge-sensitive descriptions

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
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

struct UdpSpotCheck {
  size_t row;
  char input0;
  char output;
};

static void VerifyUdpTableSpotChecks(const UdpDecl* udp,
                                     const UdpSpotCheck checks[],
                                     size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->table[checks[i].row].inputs[0], checks[i].input0);
    EXPECT_EQ(udp->table[checks[i].row].output, checks[i].output);
  }
}

TEST(ParserSection29, MixedLevelEdgeSensitive) {
  auto r = Parse(
      "primitive jk_edge_ff(output reg q, input clock, j, k, preset, clear);\n"
      "  table\n"
      "    ? ? ? 0 1 : ? : 1;\n"
      "    ? ? ? 1 0 : ? : 0;\n"
      "    r 0 0 0 0 : 0 : 1;\n"
      "    r 0 0 1 1 : ? : -;\n"
      "    f ? ? ? ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 5);
  UdpSpotCheck checks[] = {
      {0, '?', '1'},  // Level-sensitive entry
      {2, 'r', '1'},  // Edge-sensitive entry
      {4, 'f', '-'},  // Falling edge with no-change output
  };
  VerifyUdpTableSpotChecks(udp, checks, std::size(checks));
}
