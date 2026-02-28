// §11.12: Let construct

#include "fixture_parser.h"

using namespace delta;

namespace {

// let_declaration in function body
TEST(ParserA28, LetDeclInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    let inc(x) = x + 1;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #1: let_declaration
// let_declaration ::= let let_identifier [ ( [ let_port_list ] ) ] = expression
// ;
// =============================================================================
TEST(ParserA212, LetDecl_NoArgs) {
  auto r = Parse(
      "module m;\n"
      "  let addr = base + offset;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "addr");
}

TEST(ParserA212, LetDecl_EmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  let my_val() = 42;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_val");
  EXPECT_TRUE(item->func_args.empty());
}

}  // namespace
