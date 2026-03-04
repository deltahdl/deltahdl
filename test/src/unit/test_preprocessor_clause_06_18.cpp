// §6.18: User-defined types

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypedefForwardClass) {
  auto r = ParseWithPreprocessor("typedef class MyClass;\n"
                                 "class MyClass;\n"
                                 "  int x;\n"
                                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, TypedefForwardStruct) {
  auto r = ParseWithPreprocessor("module m;\n"
                                 "  typedef struct my_struct;\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypedefUnion) {
  auto r = ParseWithPreprocessor("module m;\n"
                                 "  typedef union { int i; real r; } num_t;\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// =========================================================================
// §6.18: User-defined types (typedef)
// =========================================================================
TEST(ParserSection6, TypedefLogicVector) {
  // §6.18: typedef creates a user-defined type from a built-in type.
  auto r = ParseWithPreprocessor("module t;\n"
                                 "  typedef logic [7:0] byte_t;\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

TEST(ParserSection6, TypedefUsedInVarDecl) {
  // §6.18: A typedef-defined name appears as kNamed in subsequent decls.
  auto r = ParseWithPreprocessor("module t;\n"
                                 "  typedef int counter_t;\n"
                                 "  counter_t cnt;\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto *var = r.cu->modules[0]->items[1];
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var->data_type.type_name, "counter_t");
}

} // namespace
