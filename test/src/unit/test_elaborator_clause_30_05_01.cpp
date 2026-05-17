#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelayTransitions, SingleDelayValueElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayTransitions, MinTypMaxFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayTransitions, NegativeDelayElaboratesWithoutError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = -5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayTransitions, NegativeMinTypMaxDelayElaboratesWithoutError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = -3:-2:-1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayTransitions, NegativeSpecparamDelayElaboratesWithoutError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tNeg = -4;\n"
      "    (a => b) = tNeg;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayTransitions, AllTable30_2CountsElaborate) {
  for (const char* delays : {"5", "(3, 5)", "(2, 3, 4)",
                              "(1, 2, 3, 4, 5, 6)",
                              "(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)"}) {
    ElabFixture f;
    std::string src = "module m;\n  specify\n    (a => b) = ";
    src += delays;
    src += ";\n  endspecify\nendmodule\n";
    auto* design = ElaborateSrc(src, f);
    ASSERT_NE(design, nullptr) << delays;
    EXPECT_FALSE(f.has_errors) << delays;
  }
}

}
