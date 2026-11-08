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
