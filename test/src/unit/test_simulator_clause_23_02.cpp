// §23.2

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ModuleDefinitions, MinimalModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleDefinitions, MacromoduleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc("macromodule m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
