// §30.3: Specify block declaration

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Specify block with all five item kinds elaborates
TEST(ElabA701, SpecifyBlockWithAllItemKindsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Timing checks mixed with path declarations elaborate
TEST(ElabA705, TimingChecksMixedWithPathsElaborate) {
  ElabA705Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    $setup(d, posedge clk, 10);\n"
      "    (c *> e) = 10;\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Multiple specify blocks with timing checks elaborate
TEST(ElabA705, MultipleSpecifyBlocksElaborate) {
  ElabA705Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "  endspecify\n"
      "  specify\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
