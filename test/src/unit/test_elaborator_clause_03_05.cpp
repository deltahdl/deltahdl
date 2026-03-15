// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(InterfaceDefinitions, EmptyInterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("interface ifc; endinterface\n", f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
