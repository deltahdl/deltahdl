#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

// §5 Lexical conventions

using namespace delta;

struct ParseResult5 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult5 Parse(const std::string& src) {
  ParseResult5 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk5(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// --- Unpacked range dimensions [M:N] ---

TEST(ParserCh5, UnpackedDim_Range) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:0]; endmodule"));
}

TEST(ParserCh5, UnpackedDim_MultiRange) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:2][1:3]; endmodule"));
}

TEST(ParserCh5, UnpackedDim_Typedef) {
  EXPECT_TRUE(ParseOk5("module m; typedef int triple[1:3]; endmodule"));
}

// --- Comma-separated struct members ---

TEST(ParserCh5, StructMembers_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  struct { int X, Y, Z; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(ParserCh5, StructMembers_Single) {
  EXPECT_TRUE(ParseOk5("module m; struct { int X; } s; endmodule"));
}

// --- Null module items ---

TEST(ParserCh5, ModuleBody_NullItem) {
  EXPECT_TRUE(ParseOk5("module m; ; endmodule"));
}

TEST(ParserCh5, ModuleBody_SemicolonAfterEnd) {
  EXPECT_TRUE(ParseOk5("module m; initial begin end; endmodule"));
}
