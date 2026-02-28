// §6.7: Net declarations


#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, NetCreatedFromDecl) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = 55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->type, NetType::kWire);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
