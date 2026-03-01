// §6.6.6: Supply nets

#include "fixture_parser.h"

using namespace delta;

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// 20. Supply0 and supply1 net declarations.
TEST(ParserSection6, Sec6_5_Supply0AndSupply1) {
  auto r = Parse(
      "module t;\n"
      "  supply0 gnd;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[0]->name, "gnd");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->name, "vdd");
}

}  // namespace
