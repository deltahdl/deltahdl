// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignHierarchy, UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
