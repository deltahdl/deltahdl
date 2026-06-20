#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;
namespace {

TEST(VoidDataType, VoidTypeWidthIsZero) {
  DataType dt;
  dt.kind = DataTypeKind::kVoid;
  EXPECT_EQ(EvalTypeWidth(dt), 0u);
}

TEST(VoidDataType, VoidNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
}

TEST(VoidDataType, VoidNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kVoid));
}

TEST(VoidDataType, VoidFunctionReturnsValue_Error) {
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

TEST(VoidDataType, VoidFunctionBareReturn_Ok) {
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

TEST(VoidDataType, VoidFunctionNoReturn_Ok) {
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

// A value-bearing return is rejected even when nested inside a block, since a
// void function has no return value to carry. Exercises the recursive walk of
// the function body rather than only its top-level statements.
TEST(VoidDataType, VoidFunctionNestedReturnValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void bad();\n"
      "    begin\n"
      "      return 7;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A bare return nested inside a conditional is still legal: the recursive walk
// must not mistake a value-less return for a value-bearing one.
TEST(VoidDataType, VoidFunctionConditionalBareReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    if (1) return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
