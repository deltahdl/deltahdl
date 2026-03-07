#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

// §6.13: void as function return type.
TEST(ParserSection6, VoidFunctionReturn) {
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

// §6.13: void function with body parses ok.
TEST(ParserSection6, VoidFunctionWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void greet();\n"
              "    $display(\"hello\");\n"
              "  endfunction\n"
              "endmodule\n"));
}

// §6.13: void function with arguments.
TEST(ParserSection6, VoidFunctionWithArgs) {
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

// §6.13: void type has zero width.
TEST(TypeEval, VoidTypeWidthIsZero) {
  DataType dt;
  dt.kind = DataTypeKind::kVoid;
  EXPECT_EQ(EvalTypeWidth(dt), 0u);
}

// §6.13: void is not integral.
TEST(TypeEval, VoidNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
}

// §6.13: void is not 4-state.
TEST(TypeEval, VoidNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kVoid));
}

// §6.13: void function returning a value is an error.
TEST(Elaboration, VoidFunctionReturnsValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void bad();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.13: void function with bare return is ok.
TEST(Elaboration, VoidFunctionBareReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.13: void function with no return is ok.
TEST(Elaboration, VoidFunctionNoReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    $display(\"done\");\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
