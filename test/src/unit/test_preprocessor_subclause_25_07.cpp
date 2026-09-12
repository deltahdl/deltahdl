#include "fixture_parser.h"

using namespace delta;

namespace {

// §25.7: a function prototype in an interface names a function defined
// elsewhere. The prototype stands in an interface because A.1.6's
// extern_tf_declaration is an interface_or_generate_item and no item of a
// module body, and it reaches the parser through a macro so that the case
// observes the preprocessed text rather than repeating the parser's own case
// in test_parser_subclause_25_07.cpp.
TEST(SourceText, ExternFunctionPrototypeInInterface) {
  auto r = ParseWithPreprocessor(
      "`define PROTO(name) extern function int name(input int a, int b);\n"
      "interface ifc;\n"
      "  `PROTO(compute)\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  const auto& items = r.cu->interfaces[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(items[0]->name, "compute");
  EXPECT_TRUE(items[0]->is_extern);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  EXPECT_TRUE(items[0]->func_body_stmts.empty());
}

}  // namespace
