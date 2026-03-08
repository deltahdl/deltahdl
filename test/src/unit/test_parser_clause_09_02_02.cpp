#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA602, AlwaysKeyword_AllFourVariants) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) a = 1;\n"
      "  always_comb b = 2;\n"
      "  always_latch if (en) c = 3;\n"
      "  always_ff @(posedge clk) d <= 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysCombBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysLatchBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysFFBlock));
}

TEST(ParserClause09_02_02, AlwaysKindPreserved) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) a = 1;\n"
      "  always_comb b = 2;\n"
      "  always_latch if (en) c = 3;\n"
      "  always_ff @(posedge clk) d <= 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  auto* a = FindItemByKind(items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->always_kind, AlwaysKind::kAlways);
  auto* ac = FindItemByKind(items, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(ac, nullptr);
  EXPECT_EQ(ac->always_kind, AlwaysKind::kAlwaysComb);
  auto* al = FindItemByKind(items, ModuleItemKind::kAlwaysLatchBlock);
  ASSERT_NE(al, nullptr);
  EXPECT_EQ(al->always_kind, AlwaysKind::kAlwaysLatch);
  auto* af = FindItemByKind(items, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_NE(af, nullptr);
  EXPECT_EQ(af->always_kind, AlwaysKind::kAlwaysFF);
}

TEST(ParserClause09_02_02, AlwaysFormsHaveBodies) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) a = 1;\n"
      "  always_comb b = 2;\n"
      "  always_latch if (en) c = 3;\n"
      "  always_ff @(posedge clk) d <= 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      EXPECT_NE(item->body, nullptr);
    }
  }
}

}
