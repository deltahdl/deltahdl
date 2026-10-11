

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatElaboration, StringConcatVsArrayOfStringConcat) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string S1 = \"hello\";\n"
      "  string S2 = \" world\";\n"
      "  string S;\n"
      "  string SA[2];\n"
      "  initial begin\n"
      "    S = {S1, S2};\n"
      "    SA = {S1, S2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, QueueTargetDisambiguatesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int X;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    X = {16'd1, 16'd2};\n"
      "    q = {16'd1, 16'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.2: the disambiguation is what decides whether braces are an unpacked
// array concatenation at all. The chandle target makes that decision observable
// at elaboration: because the target is an unpacked array, {c1, c2} is
// unambiguously an unpacked array concatenation (§10.10), so each operand is a
// whole chandle element and the scalar "a chandle takes only another chandle or
// null" rule does not apply. Elaboration therefore accepts it. This observes
// the rule actually being applied, not merely that some target is accepted.
TEST(UnpackedArrayConcatElaboration, ChandleArrayTargetDisambiguatedAsConcat) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle c1, c2;\n"
      "  chandle ca[2];\n"
      "  initial ca = {c1, c2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.2, negative form: with the identical right-hand side but a scalar
// (non-array) chandle target, the braces are NOT disambiguated to an unpacked
// array concatenation, so the ordinary scalar chandle-assignment rule stays in
// force and rejects {c1, c2}. The same expression accepted in the array case
// above is an error here purely because the target is not an unpacked array,
// which is exactly the distinction §10.10.2 draws. §10.10.2 states only where
// the braces are routed -- braces in an assignment-like context with an
// unpacked array target are an unpacked array concatenation, and otherwise a
// vector or string concatenation -- and prohibits nothing itself, so the report
// names the rule that does reject the source: §6.14's, that a chandle admits
// only assignment from another chandle.
TEST(UnpackedArrayConcatElaboration, ScalarChandleTargetKeepsScalarRule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle c1, c2;\n"
      "  chandle c;\n"
      "  initial c = {c1, c2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "chandle can only be assigned from another chandle or null", 4, "6.14"));
}

// §10.10.2 (printed page 265) reads braces whose target is an unpacked array
// as an unpacked array concatenation whatever names the target: an element of
// a multidimensional array and a structure's array member are such arrays,
// and a whole element of a one-dimensional array is not.
TEST(UnpackedArrayConcatElaboration, ElementArrayAndArrayMemberTargets) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int M[2][2];\n"
      "  struct { int a[2]; int b; } s;\n"
      "  int V[2];\n"
      "  initial begin M[0] = {1, 2}; s.a = {1, 2}; end\n"
      "  initial begin V[0] = {1, 2}; s.b = {1, 2}; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "unsized constant is not allowed in a "
                             "concatenation",
                             5, "11.4.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unsized constant is not allowed in a "
                            "concatenation",
                            6, "11.4.12"));
}

}  // namespace
