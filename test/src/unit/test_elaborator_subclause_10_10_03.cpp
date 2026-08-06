

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatElaboration, TypedAssignPatternInArrayConcatOk) {
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

TEST(UnpackedArrayConcatElaboration, StringConcatInStringArrayConcatOk) {
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

TEST(UnpackedArrayConcatElaboration, AssignPatternWithArrayConcatOk) {
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

TEST(UnpackedArrayConcatElaboration, ArrayIdentifierSelfDetermined) {
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

TEST(UnpackedArrayConcatElaboration, VectorConcatInByteArrayConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte BA[2];\n"
      "  initial BA = {{4'h0, 4'h6}, {4'h0, 4'hf}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, NonblockingNestedConcatError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[4];\n"
      "  initial A <= {{1, 2}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, UnpackedConcatAsAssignPatternItemOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int C[2][2];\n"
      "  initial C = '{{1, 2}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.3 (procedural, isolated): the nesting prohibition rejects a blocking
// procedural assignment whose item is itself an unpacked array concatenation.
// The inner literals are SIZED (combined width 48 != the 32-bit element), so
// this observes ONLY the nesting rule; an inner concatenation of *unsized*
// literals would additionally trip the unrelated unsized-constant-in-
// concatenation check and mask which rule did the rejecting.
TEST(UnpackedArrayConcatElaboration, ProceduralNestedConcatSizedError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  int B[9];\n"
      "  initial B = {A, {16'd4, 16'd5, 16'd6}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §10.10.3: the nesting prohibition also governs a declaration initializer,
// an assignment-like context the procedural walk never reaches. The inner
// concatenation uses sized literals whose combined width does not match the
// int element, so it cannot be reinterpreted as a self-determined vector
// concatenation — it is a nested unpacked array concatenation and is illegal.
TEST(UnpackedArrayConcatElaboration, DeclInitNestedConcatError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  int B[9] = {A, {16'd4, 16'd5, 16'd6}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// A nested concatenation whose self-determined width matches the target
// element is a vector concatenation, not an unpacked array concatenation, and
// stays legal — including when it initializes the array in its declaration.
TEST(UnpackedArrayConcatElaboration, DeclInitVectorConcatInByteArrayOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte BA[2] = {{4'h0, 4'h6}, {4'h0, 4'hf}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A flat declaration-initializer unpacked array concatenation (no item is
// itself a concatenation) is unaffected by the nesting rule.
TEST(UnpackedArrayConcatElaboration, DeclInitFlatArrayConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2] = '{10, 20};\n"
      "  int B[4] = {A, 30, 40};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
