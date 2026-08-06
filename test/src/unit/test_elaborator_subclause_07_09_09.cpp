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

// §7.9.9: two associative arrays sharing an integral (byte) index type are
// compatible. Covers an integral index type distinct from the int/string forms
// above.
TEST(AssocArrayAssignmentElaboration, AssocAssignByteIndexOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[byte];\n"
      "  int aa2[byte];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.9.9: distinct integral index types are not the same index type, so the
// assignment is rejected even though both operands are associative arrays.
TEST(AssocArrayAssignmentElaboration,
     AssocAssignIntegralIndexMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[byte];\n"
      "  int aa2[longint];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: a wildcard-indexed associative array is compatible with another
// wildcard-indexed associative array of the same element type.
TEST(AssocArrayAssignmentElaboration, AssocAssignWildcardIndexSameTypeOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[*];\n"
      "  int aa2[*];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.9.9: a wildcard index type differs from an explicit integral index type,
// so the assignment between them is rejected.
TEST(AssocArrayAssignmentElaboration, AssocAssignWildcardVsTypedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa1[*];\n"
      "  int aa2[int];\n"
      "  assign aa1 = aa2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: a queue is one of the "other types of arrays" that cannot be assigned
// to an associative array (queue source rejected).
TEST(AssocArrayAssignmentElaboration, AssocAssignFromQueueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int q[$];\n"
      "  initial aa = q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.9: nor can an associative array be assigned to a queue (queue target
// rejected).
TEST(AssocArrayAssignmentElaboration, AssocAssignToQueueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int q[$];\n"
      "  initial q = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
