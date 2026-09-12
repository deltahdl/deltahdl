#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A.1.6's extern_tf_declaration is an interface_or_generate_item and no item
// of a module body, so each prototype here stands in an interface.

TEST(FunctionDeclParsing, FuncPrototypeExternVoid) {
  auto r = Parse(
      "interface m;\n"
      "  extern function void bar();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(TaskDeclParsing, TaskPrototypeExtern) {
  auto r = Parse(
      "interface m;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "my_task");
}

TEST(TaskDeclParsing, TaskPrototypeExternNoPorts) {
  auto r = Parse(
      "interface m;\n"
      "  extern task run;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

}  // namespace
