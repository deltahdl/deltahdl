

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ElabCh10j, NestedConcatInUnpackedArrayConcatError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3], B[9];\n"
      "  initial B = {A, {4, 5, 6, 7, 8, 9}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElabCh10j, TypedAssignPatternInArrayConcatOk) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3 = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabCh10j, StringConcatInStringArrayConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string S1 = \"hello\";\n"
      "  string S2 = \" world\";\n"
      "  string SA[2];\n"
      "  initial SA = {S1, {\"foo\", S2}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabCh10j, AssignPatternWithArrayConcatOk) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2];\n"
      "  int B[2];\n"
      "  int C[2][2];\n"
      "  initial C = '{A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(ElabCh10j, ScalarElementsSelfDetermined) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabCh10j, ArrayIdentifierSelfDetermined) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2] = '{10, 20};\n"
      "  int B[4];\n"
      "  initial B = {A, 30, 40};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabCh10j, MultipleNestedConcatsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[4];\n"
      "  initial A = {{1, 2}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}
