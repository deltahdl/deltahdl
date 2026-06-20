#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssignmentCompatibleElaboration, AssignIntToLogicVector) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  logic [31:0] y;\n"
      "  initial y = x;\n"
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

TEST(AssignmentCompatibleElaboration, EnumToIntegralIsOneDirectional) {
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;
  int_t.is_signed = true;
  EXPECT_TRUE(IsAssignmentCompatible(enum_t, int_t));
  EXPECT_FALSE(IsAssignmentCompatible(int_t, enum_t));
}

}  // namespace
