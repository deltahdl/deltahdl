// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6f& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// §6.7.1: Wire with range and multiple names.
TEST(ParserSection6, Sec6_7_1_WireRangeMultipleNames) {
  auto r = Parse(
      "module t;\n"
      "  wire [3:0] x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  }
  EXPECT_EQ(items[0]->name, "x");
  EXPECT_EQ(items[1]->name, "y");
  EXPECT_EQ(items[2]->name, "z");
}

// §6.7.1: Tri net with signed qualifier and range.
TEST(ParserSection6, Sec6_7_1_TriSignedWithRange) {
  auto r = Parse(
      "module t;\n"
      "  tri signed [15:0] ts;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
}

// §6.7.1: Wand with range.
TEST(ParserSection6, Sec6_7_1_WandWithRange) {
  auto r = Parse(
      "module t;\n"
      "  wand [31:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  EXPECT_EQ(item->name, "bus");
}

// §6.7.1: Supply0 with range.
TEST(ParserSection6, Sec6_7_1_Supply0WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply0 [3:0] gnd_bus;\n"
              "endmodule\n"));
}

// §6.7.1: Supply1 with range.
TEST(ParserSection6, Sec6_7_1_Supply1WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply1 [3:0] vdd_bus;\n"
              "endmodule\n"));
}

}  // namespace
