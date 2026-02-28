// §25.7: Tasks and functions in interfaces

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// extern_tf_declaration inside a module (interface_or_generate_item applies
// to modules too via module_or_generate_item).
TEST(SourceText, ExternFunctionPrototypeInModule) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  extern function int compute(input int a, input int b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "compute");
  EXPECT_TRUE(mod->items[0]->is_extern);
  EXPECT_TRUE(mod->items[0]->func_body_stmts.empty());
}

}  // namespace
