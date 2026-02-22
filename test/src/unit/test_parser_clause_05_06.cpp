#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================

struct ParseResult506 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult506 Parse(const std::string &src) {
  ParseResult506 result;
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

static ModuleItem *FirstItem(ParseResult506 &r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserCh506, Ident_SimpleWithUnderscore) {
  auto r = Parse("module m; logic _bus3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserCh506, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(ParserCh506, Ident_CaseSensitive) {
  // Identifiers are case sensitive: X and x are different.
  auto r = Parse(
      "module m;\n"
      "  logic X;\n"
      "  logic x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "X");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "x");
}
