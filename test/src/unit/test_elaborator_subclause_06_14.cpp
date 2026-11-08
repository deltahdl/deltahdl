#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used in continuous assignment",
                            3, "6.14"));
}

TEST(ChandleDataType, ChandleSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot appear in event expression", 3,
                            "6.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleInoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(inout chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleInUntaggedUnion_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { chandle ch; int i; } my_union;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle type can only be used in tagged unions", 2,
                            "7.3.2"));
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

TEST(ChandleDataType, ChandleInsertedIntoAssociativeArray_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  initial aa[3] = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementRead_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial x = aa[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementWrite_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial aa[3] = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleScalarBitSelect_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  chandle x;\n"
      "  initial x = h[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on chandle is illegal", 4, "6.14"));
}

TEST(ChandleDataType, ChandleInPackedStruct_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { chandle ch; int i; } my_struct;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'ch' is not allowed in a packed structure", 2, "7.2.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be assigned to a non-chandle "
                            "variable",
                            4, "6.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle can only be assigned from another chandle "
                            "or null",
                            4, "6.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleRelational_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a < b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
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

TEST(ChandleDataType, ChandleAdditionInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial fork\n"
      "    r = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = a + b; r < 1; r = r + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = 0; r < 1; r = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInAssertionPassStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInAssertionFailStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) else r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial randcase\n"
      "    1 : r = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { r = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 6, "6.14"));
}

TEST(ChandleDataType, ChandleAssignedFromAnImportedFunctionResult_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  import \"DPI-C\" function chandle give();\n"
      "  chandle keep;\n"
      "  initial keep = give();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "chandle can only be assigned from another "
                             "chandle or null",
                             4, "6.14"));
}

TEST(ChandleDataType, ChandleAssignedFromANativeFunctionResult_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle keep;\n"
      "  function chandle mk();\n"
      "    return null;\n"
      "  endfunction\n"
      "  initial keep = mk();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "chandle can only be assigned from another "
                             "chandle or null",
                             6, "6.14"));
}

TEST(ChandleDataType, ImportedFunctionChandleResultAssignedToInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  import \"DPI-C\" function chandle give();\n"
      "  chandle keep;\n"
      "  int r;\n"
      "  initial r = give();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be assigned to a non-chandle "
                            "variable",
                            5, "6.14"));
}

TEST(ChandleDataType, ChandleInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "chandle c; wire w;", "assign w = c;"},
      "chandle cannot be used in continuous assignment", "6.14"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "chandle c; logic y;", "always @(c) y = 0;"},
      "chandle cannot appear in event expression", "6.14"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "chandle c; logic y;", "always @(c == null) y = 0;"}));
}

}  // namespace
