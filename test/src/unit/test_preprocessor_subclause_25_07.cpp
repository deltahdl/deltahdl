#include "fixture_parser.h"

using namespace delta;

namespace {

// §25.7: a function prototype in an interface names a function defined
// elsewhere. The prototype stands in an interface because A.1.6's
// extern_tf_declaration is an interface_or_generate_item and no item of a
// module body.
TEST(SourceText, ExternFunctionPrototypeInInterface) {
  auto r = ParseWithPreprocessor(
      "interface ifc;\n"
      "  extern function int compute(input int a, input int b);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(ifc->items[0]->name, "compute");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

}  // namespace
