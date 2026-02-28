// §30.4.6: Declaring multiple module paths in a single statement

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Mixed terminal forms do not interfere with behavioral simulation
TEST(SimA703, MixedTerminalFormsDoNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  specify\n"
      "    (x[3:0], intf.sig *> y[0], z) = 5;\n"
      "    (posedge clk => (q[0] : d)) = 3;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 11u}, {"b", 22u}});
}

}  // namespace
