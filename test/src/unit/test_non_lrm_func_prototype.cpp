// §non-lrm:func_prototype

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA26, FuncPrototypeExternVoid) {
  auto r = Parse(
      "module m;\n"
      "  extern function void bar();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// ---------------------------------------------------------------------------
// task_prototype ::=
//   task [ dynamic_override_specifiers ] task_identifier
//     [ ( [ tf_port_list ] ) ]
// ---------------------------------------------------------------------------
TEST(ParserA27, TaskPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "my_task");
}

TEST(ParserA27, TaskPrototypeExternNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  extern task run;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

}  // namespace
