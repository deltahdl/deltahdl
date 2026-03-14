#include "fixture_elaborator.h"

namespace {

// §3.1 General — overview-level elaboration test verifying the simplest
// building block can be compiled and elaborated end-to-end.

TEST(BuildingBlockElaboration, MinimalModuleElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
