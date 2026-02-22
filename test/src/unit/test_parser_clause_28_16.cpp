// Tests for §28.16 — Gate delay specifications (two/three/min:typ:max)

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

TEST(ParserSection28, GateWithTwoDelays) {
  auto r = Parse("module m;\n"
                 "  and #(10, 12) a2(out, in1, in2);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateWithThreeDelays) {
  auto r = Parse("module m;\n"
                 "  bufif0 #(10, 12, 11) b3(out, in, ctrl);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateMinTypMaxDelay) {
  auto r = Parse("module m;\n"
                 "  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1(io1, io2, dir);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}
