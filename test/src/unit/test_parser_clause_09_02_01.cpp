// §9.2.1: Initial procedures

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;
// Helpers to extract items from the first module.
static ModuleItem* FindItem(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}
namespace {

// =============================================================================
// A.6.2 Production: initial_construct
// initial_construct ::= initial statement_or_null
// =============================================================================
TEST(ParserA602, InitialConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}
TEST(Parser, ModuleWithInitialBlock) {
  auto r = Parse(
      "module hello;\n"
      "  initial $display(\"Hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}
TEST(ParserSection9b, StructuredProcMultipleInitial) {
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
    if (item->kind == ModuleItemKind::kInitialBlock) count++;
  }
  EXPECT_EQ(count, 3);
}

// =============================================================================
// LRM section 9.2 -- Structured procedures (ParseOk smoke tests)
// Various procedure forms that should parse without errors.
// =============================================================================
TEST(ParserSection9c, InitialWithTaskCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task;\n"
              "    #10 a = 1;\n"
              "  endtask\n"
              "  initial begin\n"
              "    my_task;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.2.1 -- Initial and final blocks
// =============================================================================
TEST(ParserSection9, InitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
