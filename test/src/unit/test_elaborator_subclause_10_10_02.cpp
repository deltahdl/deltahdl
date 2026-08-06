

#include "fixture_elaborator.h"

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
// which is exactly the distinction §10.10.2 draws.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
