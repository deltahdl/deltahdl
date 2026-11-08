#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

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

TEST(VoidDataType, VoidMemberInTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, SoleVoidMemberInTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { void None; } Opt;\n"
      "  Opt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, VoidMemberInPackedTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed { void Invalid; bit [31:0] Valid; } "
      "VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
