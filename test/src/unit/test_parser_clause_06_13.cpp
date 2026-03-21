#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

TEST(VoidDataType, VoidFunctionReturn) {
  auto r = Parse(
      "module t;\n"
      "  function void do_nothing();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(VoidDataType, VoidFunctionWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void greet();\n"
              "    $display(\"hello\");\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(VoidDataType, VoidFunctionWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  function void set_val(input int x);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(item->func_args.size(), 1u);
}

}  // namespace
