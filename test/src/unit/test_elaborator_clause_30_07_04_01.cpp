#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA701, SpecifyBlockWithPulsestyleElaborates) {
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

}  // namespace
