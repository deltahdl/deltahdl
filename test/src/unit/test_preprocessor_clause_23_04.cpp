// §23.4: Nested modules

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Nested module_declaration as non_port_module_item.
TEST(SourceText, NestedModuleDeclaration) {
  auto r = ParseWithPreprocessor(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->nested_module_decl, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->nested_module_decl->name, "inner");
}

}  // namespace
