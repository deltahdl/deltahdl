#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.5.1: a single path delay value is valid and represents the typical
// delay — elaboration should accept it without error.
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

// §30.5.1: colon-separated form expresses min/typ/max — elaboration accepts
// the form regardless of the configured delay selection mode.
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

// §30.5.1: a negative delay expression is valid syntax — it shall be treated
// as zero at runtime, not rejected by elaboration.
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

// §30.5.1: a min:typ:max expression with negative components is accepted —
// the negative-to-zero clamp is a runtime rule, not an elaboration rule.
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

// §30.5.1: a specparam that evaluates negatively must not cause elaboration
// to fail; the clamp is applied when the value is consumed at runtime.
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

// §30.5.1: all transition-count forms listed in Table 30-2 (1, 2, 3, 6, 12)
// elaborate without error when the syntax is otherwise well-formed.
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

}  // namespace
