#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(SupplyNetE2e, Supply1OutranksExplicitStrongDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  supply1 vdd;\n"
                      "  logic result;\n"
                      "  buf (strong0, strong1) g (vdd, 1'b0);\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = vdd;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

}  // namespace
