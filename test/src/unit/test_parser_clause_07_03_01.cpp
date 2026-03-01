// §7.3.1: Packed unions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA221, StructUnionUnionSoft) {
  auto r = Parse(
      "module m;\n"
      "  union soft { int a; real b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_soft);
}

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection7, UnionSoftPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    bit [7:0] a;\n"
      "    bit [3:0] b;\n"
      "  } soft_u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_soft);
  EXPECT_TRUE(item->typedef_type.is_packed);
}

// =========================================================================
// §7.3.1: Packed unions
// =========================================================================
TEST(ParserSection7, UnionPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef union packed {\n"
      "    logic [31:0] word;\n"
      "    logic [3:0] [7:0] bytes;\n"
      "  } word_u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

}  // namespace
