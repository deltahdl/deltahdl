// §7.2.1: Packed structures


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// § primary — member access (struct field)
TEST(SimA84, PrimaryMemberAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x;\n"
      "  initial begin p = 16'hABCD; x = p.hi; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

}  // namespace
