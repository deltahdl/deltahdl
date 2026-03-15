// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(CheckerDefinitions, EmptyCheckerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker\n", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
