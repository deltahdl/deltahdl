#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_scheduler.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.6.6: supply0 nets shall have supply strength on the 0 they drive.
TEST(SupplyNetResolution, Supply0CarriesSupplyStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kSupply);
}

// §6.6.6: supply1 nets shall have supply strength on the 1 they drive.
TEST(SupplyNetResolution, Supply1CarriesSupplyStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply1;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0));
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kSupply);
}

// --- Real-source, full-pipeline observation of §6.6.6 ---
//
// The synthetic cases above pin the resolved strength to supply by handing
// ResolveSupplyNet a Net object directly. The property §6.6.6 actually defines
// -- that a declared supply0/supply1 net carries *supply* strength, the
// strongest drive level in the §28.11 strength model -- is only observable when
// a real declaration meets a competing driver. Supply outranks strong, so a
// strong driver of the opposite value cannot move the net. These cases build
// the input the way real source does (a supply net declaration plus a
// continuous assignment, consuming §28.11's drive model) and run it through
// parse -> elaborate -> lower -> run, reading the resolved net back.

// §6.6.6: a strong-1 continuous driver on a supply0 net loses to the net's
// supply-strength 0. The same `assign w = 1'b1` on an ordinary wire would read
// 1; that it reads 0 here is exactly what supply strength buys.
TEST(SupplyNetE2e, Supply0OutranksStrongOneDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply0 gnd;\n"
                      "  logic result;\n"
                      "  assign gnd = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = gnd;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §6.6.6 mirror: a strong-0 continuous driver on a supply1 net loses to the
// net's supply-strength 1.
TEST(SupplyNetE2e, Supply1OutranksStrongZeroDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply1 vdd;\n"
                      "  logic result;\n"
                      "  assign vdd = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = vdd;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.6: the supply strength holds across every bit of a vector supply net. A
// strong-0 driver on all four bits of a supply1 bus is overridden bit for bit,
// so the bus reads 4'b1111.
TEST(SupplyNetE2e, Supply1VectorHoldsSupplyStrengthPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply1 [3:0] bus;\n"
                      "  logic [3:0] result;\n"
                      "  assign bus = 4'b0000;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = bus;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xFu);
}

// §6.6.6 vector input form, supply0 side: a strong-1 driver across all four
// bits of a supply0 bus loses bit for bit to the net's supply-strength 0, so
// the bus reads 4'b0000 (the mirror of the supply1 vector case).
TEST(SupplyNetE2e, Supply0VectorHoldsSupplyStrengthPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply0 [3:0] bus;\n"
                      "  logic [3:0] result;\n"
                      "  assign bus = 4'b1111;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = bus;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x0u);
}

// §6.6.6 consuming §28.11: the competing driver is written with §28.11's
// explicit drive-strength syntax rather than left at the default. Even a driver
// declared (strong1, strong0) -- the strongest ordinary drive level -- is below
// supply, so a strong-0 driver on a supply1 net still reads 1. Building the
// driver from the dependency's real strength syntax exercises the
// drive-strength parse/elaborate path through the full pipeline.
TEST(SupplyNetE2e, Supply1OutranksExplicitStrongDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply1 vdd;\n"
                      "  logic result;\n"
                      "  assign (strong1, strong0) vdd = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = vdd;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

}  // namespace
