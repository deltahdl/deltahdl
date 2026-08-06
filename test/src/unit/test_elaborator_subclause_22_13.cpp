#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §22.13: `__LINE__ expands to the current input line number as a simple
// decimal number. The preprocessor tests observe the expanded text directly;
// here we fold that decimal into an elaboration-time constant (a packed
// dimension) and check the resulting vector width. The width equals the decimal
// line number, so the assertions discriminate whether `__LINE__ was actually
// expanded to that form by the preprocessor before elaboration. (Claim A,
// `__FILE__ expanding to a string literal, is observed by value at the
// preprocessor and simulator stages; it does not fold to an elaboration
// constant here.)

// Claim B: the decimal produced by `__LINE__ is consumed as a constant. The
// directive sits on source line 3, so [`__LINE__ - 1:0] elaborates to 3 bits.
TEST(FileAndLineMacroElaboration, LineDecimalSizesElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  logic a;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[1].name, "wide");
  EXPECT_EQ(mod->variables[1].width, 3u);
}

// Claim B, discriminating: pushing the macro one line further yields a 4-bit
// vector, so the width tracks the actual source line rather than a fixed value.
TEST(FileAndLineMacroElaboration, LineDecimalTracksSourceLine) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[2].name, "wide");
  EXPECT_EQ(mod->variables[2].width, 4u);
}

}  // namespace
