#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.22.3: "All equivalent types, and all nonequivalent types that have
// implicit casting rules defined between them, are assignment-compatible
// types. For example, all integral types are assignment compatible."
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

// §6.22.3: real and integral types share an implicit casting rule, so a
// real-to-int assignment is assignment-compatible (with rounding).
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

// §6.22.3: integral types are assignment compatible with each other in both
// directions, so int ↔ bit signed [31:0] is interchangeable via assignment
// (the §6.22 example that defers to §6.22.3 for the mechanism).
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

// §6.22.3: "Compatibility can be in one direction only. For example, an
// enum can be converted to an integral type without a cast, but not the
// other way around." The IsAssignmentCompatible predicate that the
// elaborator delegates to for port-connection checks shall reflect this
// asymmetry.
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
