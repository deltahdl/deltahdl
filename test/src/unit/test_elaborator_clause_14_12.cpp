#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultClockingElab, DuplicateDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
