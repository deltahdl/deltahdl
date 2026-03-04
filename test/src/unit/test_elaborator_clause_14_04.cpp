#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA611, SkewVariationsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step data;\n"
      "    output negedge #1 ack;\n"
      "    input posedge ready;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
