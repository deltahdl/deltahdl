// §10.3.1: The net declaration assignment

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfNetDeclAssignmentsWithInit) {
  auto r = Parse("module m; wire a = 1'b0, b = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserA24, NetDeclAssignmentWithInit) {
  auto r = Parse("module m; wire w = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserA24, NetDeclAssignmentDimsAndInit) {
  auto r = Parse("module m; wire [7:0] mem [0:3] = '{0,1,2,3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection6, NetWithImplicitContAssign) {
  // §6.5: Unlike nets, a variable cannot have an implicit continuous
  // assignment. Wire with inline assignment is a net continuous assign.
  auto r = Parse(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
