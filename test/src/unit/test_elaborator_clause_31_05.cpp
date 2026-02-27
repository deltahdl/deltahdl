// §31.5: Edge-control specifiers

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// edge_control_specifier with x transitions elaborates
TEST(ElabA70503, EdgeControlSpecifierXTransitionsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [x0, x1] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
