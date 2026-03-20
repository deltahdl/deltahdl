#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CycleDelayElab, WithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
