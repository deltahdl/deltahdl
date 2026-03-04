// §23.2.4: Module contents

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §8.3 — Class inside module
TEST(ParserSection8, ClassInsideModule) {
  auto r = Parse("module m;\n"
                 "  class inner_cls;\n"
                 "    int x;\n"
                 "  endclass\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto *cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  EXPECT_EQ(cls->name, "inner_cls");
}
TEST(ParserSection23, ModuleDefinitionWithBody) {
  auto r = Parse("module m;\n"
                 "  wire a;\n"
                 "  assign a = 1'b0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
}
static bool HasItemKind(ParseResult &r, ModuleItemKind kind) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == kind)
      return true;
  }
  return false;
}

TEST(ParserSection9c, MixedProcedureTypes) {
  auto r = Parse("module m;\n"
                 "  initial a = 0;\n"
                 "  always @(posedge clk) q <= d;\n"
                 "  final $display(\"done\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kFinalBlock));
}

} // namespace
