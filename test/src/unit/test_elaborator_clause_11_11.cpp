#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MinTypMaxElaboration, ContinuousAssignDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2:3) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, SpecparamConstantMinTypMax) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tpd = 1:2:3;\n"
      "  endspecify\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MinTypMaxElaboration, GateDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  and #(2:3:4) g1(c, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
