// §7.10.4

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §10.10: Empty concatenation clears a queue.
TEST(SimCh10j, EmptyConcatClearsQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q = {1, 2, 3};\n"
      "    q = {};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

}  // namespace
