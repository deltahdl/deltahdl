#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(StructuredProcedureParsing, AllSixProcedureTypes) {
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

TEST(StructuredProcedureParsing, NoLimitOnProcedureCount) {
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

TEST(StructuredProcedureParsing, FinalBlockParsing) {
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

TEST(StructuredProcedureParsing, MultipleFinalBlocks) {
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

TEST(StructuredProcedureParsing, MixedProcedureOrdering) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always #5 clk = ~clk;\n"
      "  initial a = 0;\n"
      "  final $display(\"end\");\n"
      "  initial b = 1;\n"
      "  always_comb a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysCombBlock));
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kInitialBlock), 2u);
}

TEST(StructuredProcedureParsing, AlwaysWithStatement) {
  auto r = Parse(
      "module m;\n"
      "  always #10 clk = ~clk;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

}  // namespace
