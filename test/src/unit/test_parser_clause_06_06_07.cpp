// §6.6.7: User-defined nettypes

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

namespace {

TEST(Parser, NettypeDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
}

TEST(Parser, NettypeWithResolutionFunction) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet with resolve_fn;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

TEST(Parser, NettypeUsedInDecl) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto *item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}

}  // namespace
