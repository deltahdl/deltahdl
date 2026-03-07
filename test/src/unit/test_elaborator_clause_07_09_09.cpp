#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.9.9: Assoc-to-assoc assignment with same type/index is OK.
TEST(Elaboration, AssocAssignSameTypeOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[string];\n"
      "  int aa2[string];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.9.9: Assoc-to-fixed-size array assignment is rejected.
TEST(Elaboration, AssocToFixedArrayAssign_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  int fa[4];\n"
      "  assign fa = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: Fixed-size to assoc assignment is rejected.
TEST(Elaboration, FixedArrayToAssocAssign_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  int fa[4];\n"
      "  assign aa = fa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: Assoc arrays with different index types are rejected.
TEST(Elaboration, AssocAssignIndexTypeMismatch_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[string];\n"
      "  int aa2[int];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: Assoc arrays with same int index and same element type is OK.
TEST(Elaboration, AssocAssignIntIndexOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[int];\n"
      "  int aa2[int];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
