// §10.4.1: Blocking procedural assignments

#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// assignment_pattern in procedural assignment — simulation
// ---------------------------------------------------------------------------
// §10.9: assignment pattern in blocking assignment
TEST(SimA60701, PatternInBlockingAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 11u);
  EXPECT_EQ(b->value.ToUint64(), 22u);
}

}  // namespace
