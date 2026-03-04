// §9.2: Structured procedures

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;
namespace {

TEST(ParserA602, InitialConstruct_Multiple) {
  // Multiple initial blocks in the same module
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
// =============================================================================
// §9.2 -- Structured procedures (initial, always, final)
// =============================================================================
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

// =============================================================================
// LRM section 9.2 -- Structured procedures overview
// Multiple initial/always procedures coexist within a module.
// =============================================================================
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

}  // namespace
