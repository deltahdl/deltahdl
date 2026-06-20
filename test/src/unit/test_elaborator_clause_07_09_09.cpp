#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssocArrayAssignmentElaboration, AssocAssignSameTypeOk) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignIndexTypeMismatchRejected) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignIntIndexOk) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignClassIndexSameTypeOk) {
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

TEST(AssocArrayAssignmentElaboration,
     AssocAssignClassIndexDifferentTypeRejected) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignClassIndexMixedTypeRejected) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignElementTypeMismatchRejected) {
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

TEST(AssocArrayAssignmentElaboration, AssocAssignFromFixedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int fa[4];\n"
      "  initial aa = fa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssocArrayAssignmentElaboration, AssocAssignToFixedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int fa[4];\n"
      "  initial fa = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssocArrayAssignmentElaboration, AssocAssignFromDynamicRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int da[];\n"
      "  initial aa = da;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssocArrayAssignmentElaboration, AssocAssignToDynamicRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int da[];\n"
      "  initial da = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
