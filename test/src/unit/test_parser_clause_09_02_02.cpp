// §9.2.2: Always procedures

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

// =============================================================================
// A.6.2 Production: always_keyword
// always_keyword ::= always | always_comb | always_latch | always_ff
// =============================================================================
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
  auto blocks =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_EQ(blocks.size(), 4u);
  EXPECT_EQ(blocks[0]->always_kind, AlwaysKind::kAlways);
  EXPECT_EQ(blocks[1]->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(blocks[2]->always_kind, AlwaysKind::kAlwaysLatch);
  EXPECT_EQ(blocks[3]->always_kind, AlwaysKind::kAlwaysFF);
}

}  // namespace
