// §30.7.4.2: Negative pulse detection

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Specify block with showcancelled declaration elaborates
TEST(ElabA701, SpecifyBlockWithShowcancelledElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1;\n"
      "    noshowcancelled out2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
