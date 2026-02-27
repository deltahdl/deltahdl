// §30.4.4.4: The ifnone condition

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// State-dependent path (ifnone) elaborates
TEST(ElabA702, StateDependentIfnonePathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
