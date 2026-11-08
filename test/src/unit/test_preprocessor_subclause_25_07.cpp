#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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
