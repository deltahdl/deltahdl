// Tests for §28.10 — Gate delays (parenthesized form)

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

TEST(ParserSection28, GateWithParenDelay) {
  auto r = Parse("module m;\n"
                 "  or #(10) g1(out, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, StrengthSpecSupply) {
  auto r = Parse("module m;\n"
                 "  nand (supply0, supply1) g1(out, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5); // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5); // supply1 = 5
}

TEST(ParserSection28, StrengthSpecHighz) {
  auto r = Parse("module m;\n"
                 "  or (highz0, pull1) g1(out, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1); // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 3); // pull1 = 3
}
