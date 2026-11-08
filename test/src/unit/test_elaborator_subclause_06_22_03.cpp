#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentCompatibleElaboration, FunctionReturnAcceptsIntegralValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, FunctionReturnRejectsIncompatibleValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function string f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            3, "12.8"));
}

TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsRealValueIntoIntegral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    return 3.5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsIntegralValueIntoReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function real f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration,
     FunctionReturnRejectsStringValueIntoIntegral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    string s;\n"
      "    return s;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsSizedSignedVectorType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function bit signed [31:0] f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, AssignRealToInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial i = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, IntAndBitSignedAreInterchangeable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  bit signed [31:0] y;\n"
      "  initial begin\n"
      "    x = y;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, EquivalentTypesAreCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  EXPECT_TRUE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleElaboration, IntegralCompatibilityIsSymmetric) {
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  DataType l;
  l.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(i, l));
  EXPECT_TRUE(IsAssignmentCompatible(l, i));

  DataType byte_t;
  byte_t.kind = DataTypeKind::kByte;
  DataType shortint_t;
  shortint_t.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(byte_t, shortint_t));
  EXPECT_TRUE(IsAssignmentCompatible(shortint_t, byte_t));
}

TEST(AssignmentCompatibleElaboration, RealAndIntegralNumericConversion) {
  DataType real_t;
  real_t.kind = DataTypeKind::kReal;
  DataType logic_t;
  logic_t.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(real_t, logic_t));
  EXPECT_TRUE(IsAssignmentCompatible(logic_t, real_t));

  DataType shortreal_t;
  shortreal_t.kind = DataTypeKind::kShortreal;
  DataType realtime_t;
  realtime_t.kind = DataTypeKind::kRealtime;
  EXPECT_TRUE(IsAssignmentCompatible(real_t, shortreal_t));
  EXPECT_TRUE(IsAssignmentCompatible(realtime_t, shortreal_t));
}

TEST(AssignmentCompatibleElaboration, EnumToIntegralIsOneDirectional) {
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;
  int_t.is_signed = true;
  DataType logic_t;
  logic_t.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(enum_t, int_t));
  EXPECT_TRUE(IsAssignmentCompatible(enum_t, logic_t));
  EXPECT_FALSE(IsAssignmentCompatible(int_t, enum_t));
  EXPECT_FALSE(IsAssignmentCompatible(logic_t, enum_t));
}

TEST(AssignmentCompatibleElaboration, UnrelatedTypesAreNotCompatible) {
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;

  DataType string_t;
  string_t.kind = DataTypeKind::kString;
  EXPECT_FALSE(IsAssignmentCompatible(string_t, int_t));

  DataType chandle_t;
  chandle_t.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsAssignmentCompatible(chandle_t, int_t));

  DataType event_t;
  event_t.kind = DataTypeKind::kEvent;
  EXPECT_FALSE(IsAssignmentCompatible(event_t, int_t));
}

}  // namespace
