#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleWidth64) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(ChandleDataType, ChandleNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandleNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandlePort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(input chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleIsChandle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_chandle);
}

TEST(ChandleDataType, ChandleVarDecl_OK) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleToChandleAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssignNull_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  initial h = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleOutputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(output chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(inout chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInUntaggedUnion_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { chandle ch; int i; } my_union;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInTaggedUnion_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { chandle Ch; int I; } my_union;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInPackedStruct_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { chandle ch; int i; } my_struct;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssignToInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial x = h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, IntAssignToChandle_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial h = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAddition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleBitwiseOr_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a;\n"
      "  int r;\n"
      "  initial r = a | 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleUnaryNot_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = ~h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a == b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h != null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h === null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h !== null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
