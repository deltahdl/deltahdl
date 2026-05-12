#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(Elaboration, AssocAssignClassIndex_SameTypeOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  class K;\n"
             "    int id;\n"
             "  endclass\n"
             "  int aa[K];\n"
             "  int bb[K];\n"
             "  assign aa = bb;\n"
             "endmodule\n"));
}

TEST(Elaboration, AssocAssignClassIndex_DifferentTypeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class A;\n"
      "    int id;\n"
      "  endclass\n"
      "  class B;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[A];\n"
      "  int bb[B];\n"
      "  assign aa = bb;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, AssocAssignClassIndex_MixedTypeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class K;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[K];\n"
      "  int bb[int];\n"
      "  assign aa = bb;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, AssocAssignElementTypeMismatch_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[int];\n"
      "  logic [7:0] aa2[int];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
