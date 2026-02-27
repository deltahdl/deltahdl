// §30.4.4.2: Simple state-dependent paths

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// State-dependent path (if) elaborates
TEST(ElabA702, StateDependentIfPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § unary/binary_module_path_operator — specify block elaborates
TEST(ElabA86, ModulePathOperatorsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a && b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
