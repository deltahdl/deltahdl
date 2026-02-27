// §31.8: Vector signals in timing checks

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Terminal with part select elaborates
TEST(ElabA70503, TerminalPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[3:0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
