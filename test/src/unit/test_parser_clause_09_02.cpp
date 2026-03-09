#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA602, InitialConstruct_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto inits =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(inits.size(), 3u);
}

TEST(ParserSection9b, StructuredProcInitialAndAlways) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kAlwaysBlock);
}

TEST(ParserSection9c, MultipleInitialProcedures) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 1;\n"
      "  initial c = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) ++count;
  }
  EXPECT_EQ(count, 3);
}

TEST(ParserClause09_02, Syntax9_1_AllSixProcedureTypes) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b, c, d, e;\n"
      "  initial a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always_comb b = c & d;\n"
      "  always_latch if (clk) e = a;\n"
      "  always_ff @(posedge clk) c <= a;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysCombBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysLatchBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysFFBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFinalBlock));
}

TEST(ParserClause09_02, NoLimitOnProcedureCount) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "  initial d = 0;\n"
      "  initial e = 0;\n"
      "  always #1 a = ~a;\n"
      "  always #2 b = ~b;\n"
      "  always #3 c = ~c;\n"
      "  always #4 d = ~d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kInitialBlock), 5u);
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kAlwaysBlock), 4u);
}

TEST(ParserClause09_02, FinalBlockParsing) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"end\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserClause09_02, MultipleFinalBlocks) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"a\");\n"
      "  final $display(\"b\");\n"
      "  final $display(\"c\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock),
      3u);
}

TEST(ParserClause09_02, AlwaysKeywordVariants) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a;\n"
      "  always #5 clk = ~clk;\n"
      "  always_comb a = 0;\n"
      "  always_latch if (clk) a = 1;\n"
      "  always_ff @(posedge clk) a <= 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlways));
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlwaysComb));
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlwaysLatch));
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlwaysFF));
}

}  // namespace
