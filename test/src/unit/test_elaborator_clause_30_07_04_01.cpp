#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclElaboration, SpecifyBlockWithPulsestyleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "    pulsestyle_ondetect out2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, PulsestyleOnModulePathOutputIsError) {
  // An output driven by a module path cannot also carry a pulsestyle
  // declaration: both mechanisms would try to own the pulse semantics
  // for the same destination, so the elaborator must reject the combo.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_onevent o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
