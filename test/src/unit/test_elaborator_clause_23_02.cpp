// §23.2

#include "fixture_elaborator.h"

namespace {

// §3.1 General — overview-level elaboration tests.
TEST(ModuleDefinition, MinimalModuleElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleDefinitions, MacromoduleElaborates) {
  EXPECT_TRUE(ElabOk("macromodule m; endmodule\n"));
}

}  // namespace
