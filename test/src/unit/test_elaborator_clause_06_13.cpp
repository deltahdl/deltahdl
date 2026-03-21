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

}  // namespace
