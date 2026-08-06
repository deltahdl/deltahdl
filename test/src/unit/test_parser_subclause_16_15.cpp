#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SourceText, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

// §16.15: a default disable iff may also be declared within a generate block.
// The grammar left-hand side is module_or_generate_item_declaration, so the
// parser accepts the declaration in a generate-block body exactly as in a
// module body. Real source is driven through the parser and the nested item is
// checked to be the default disable iff production.
TEST(SourceText, DefaultDisableIffInGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  bit rst;\n"
      "  if (1) begin\n"
      "    default disable iff rst;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* gen = nullptr;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kGenerateIf) {
      gen = it;
      break;
    }
  }
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(gen->gen_body[0]->init_expr, nullptr);
}

// §16.15: the declaration is legal directly within an interface body -- one of
// the enumerated syntactic positions. The parser accepts it via the shared
// module-item path.
TEST(SourceText, DefaultDisableIffInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  default disable iff rst;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->interfaces[0]->items[0]->init_expr, nullptr);
}

// §16.15: and directly within a program body -- the remaining enumerated
// declaration position.
TEST(SourceText, DefaultDisableIffInProgram) {
  auto r = Parse(
      "program p;\n"
      "  default disable iff rst;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->programs[0]->items[0]->init_expr, nullptr);
}

}  // namespace
