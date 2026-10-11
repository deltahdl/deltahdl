

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

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

// §10.10.3 (printed page 266): a complete unpacked array concatenation is no
// item of another, and braces holding an unpacked array are one, written in a
// nonblocking assignment as in a blocking one.
TEST(UnpackedArrayConcatElaboration, NonblockingNestedConcatError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[4]; int P[2];\n"
      "  initial A <= {{P, P}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nested concatenation in unpacked array "
                            "concatenation is not self-determined",
                            3, "10.10.3"));
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

// §10.10.3 (printed page 266): inner braces are a vector concatenation, a
// self-determined item of whatever width assigned to one element, so A's three
// elements and one 48-bit item fill a four-element array, assigned by a
// procedure or initializing the array in its declaration.
TEST(UnpackedArrayConcatElaboration, NestedConcatOfAnyWidthIsOneElement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  int B[4] = {A, {16'd4, 16'd5, 16'd6}};\n"
      "  int C[4];\n"
      "  initial C = {A, {16'd4, 16'd5, 16'd6}};\n"
      "  int q[$]; byte BA[2];\n"
      "  initial begin q = {{8'd1, 8'd2}}; BA = {{8'h1, 8'h2}, 8'h3}; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FindDiag(f, "is not self-determined"), nullptr);
}

// §10.10.3 holds the declaration's initializer to the nesting prohibition as
// it holds a procedural assignment.
TEST(UnpackedArrayConcatElaboration, DeclInitNestedConcatError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  int B[9] = {A, {A, A}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nested concatenation in unpacked array "
                            "concatenation is not self-determined",
                            3, "10.10.3"));
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
