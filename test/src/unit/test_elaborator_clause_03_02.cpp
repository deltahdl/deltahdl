// §3.2

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §3.2 Design elements — simulation of design element building blocks.
TEST(DesignElementSim, MinimalModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc("module t; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
