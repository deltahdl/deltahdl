#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypedefForwardClass) {
  auto r = ParseWithPreprocessor(
      "typedef class MyClass;\n"
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, TypedefForwardStruct) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  typedef struct my_struct;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypedefUnion) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  typedef union { int i; real r; } num_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypedefLogicVector) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

TEST(ParserSection6, TypedefUsedInVarDecl) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  typedef int counter_t;\n"
      "  counter_t cnt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* var = r.cu->modules[0]->items[1];
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var->data_type.type_name, "counter_t");
}

TEST(ParserSection6, InterfaceBasedTypedef) {
  auto r = ParseWithPreprocessor(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypedefChainPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  typedef logic [15:0] halfword_t;\n"
      "  typedef halfword_t addr_t;\n"
      "  addr_t pc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* var = r.cu->modules[0]->items[2];
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var->data_type.type_name, "addr_t");
}

}  // namespace
