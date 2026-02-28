// §9.3.5: Statement labels


#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// Sim test fixture
namespace {

// §12.3: labeled statements execute normally
TEST(SimA604, LabeledStatementExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    step1: x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
