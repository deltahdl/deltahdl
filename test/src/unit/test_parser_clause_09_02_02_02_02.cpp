#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection9, Sec9_2_2_2_BothFormsWithBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, c, x, y;\n"
      "  always_comb begin\n"
      "    x = a + b;\n"
      "  end\n"
      "  always @(*) begin\n"
      "    y = b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* comb = NthAlwaysItem(r, 0);
  auto* star = NthAlwaysItem(r, 1);
  ASSERT_NE(comb, nullptr);
  ASSERT_NE(star, nullptr);
  EXPECT_EQ(comb->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(star->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(comb->body, nullptr);
  ASSERT_NE(star->body, nullptr);
  EXPECT_EQ(comb->body->kind, StmtKind::kBlock);
  EXPECT_EQ(star->body->kind, StmtKind::kBlock);
}

TEST(ParserSection9, Sec9_2_2_2_FullComboModuleParseOk) {
  EXPECT_TRUE(
      ParseOk("module combo_module;\n"
              "  logic [3:0] sel, a, b, c, d;\n"
              "  logic [3:0] out1, out2, out3;\n"
              "  always_comb begin\n"
              "    int tmp;\n"
              "    tmp = a + b;\n"
              "    case (sel)\n"
              "      4'b0001: out1 = a;\n"
              "      4'b0010: out1 = b;\n"
              "      default: out1 = 0;\n"
              "    endcase\n"
              "  end\n"
              "  always @* begin\n"
              "    int tmp2;\n"
              "    tmp2 = c - d;\n"
              "    if (sel[0])\n"
              "      out2 = c;\n"
              "    else\n"
              "      out2 = d;\n"
              "  end\n"
              "  always @(*) begin\n"
              "    out3 = a ^ b ^ c ^ d;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9, Sec9_2_2_2_AlwaysStarAlwaysKind) {
  auto r = Parse(
      "module m;\n"
      "  always @* a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
}

static ModuleItem* NthAlwaysItem(ParseResult& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

TEST(ParserSection9, Sec9_2_2_2_SideBySideBothForms) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a & b;\n"
      "  always @* y = c | d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(second->always_kind, AlwaysKind::kAlways);
}

TEST(ParserSection9, Sec9_2_2_2_SideBySideBodiesExist) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a;\n"
      "  always @* y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
  EXPECT_EQ(first->body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(second->body->kind, StmtKind::kBlockingAssign);
}

}  // namespace
