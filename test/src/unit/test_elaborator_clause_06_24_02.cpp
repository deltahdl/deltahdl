// §6.24.2: $cast dynamic casting

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.24.2: $cast function form returns 1 on valid enum cast.
TEST(SimCh6, CastEnumSuccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = $cast(c, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

}  // namespace
