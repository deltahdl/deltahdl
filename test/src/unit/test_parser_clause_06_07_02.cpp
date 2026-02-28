// §6.7.2: Net declarations with user-defined nettypes

#include "fixture_parser.h"

using namespace delta;

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(Parser, NettypeUsedInDecl) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}

}  // namespace
