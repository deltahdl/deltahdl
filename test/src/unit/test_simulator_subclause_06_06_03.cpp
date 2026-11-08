#include <gtest/gtest.h>

#include "helpers_scheduler.h"
#include "simulator/net.h"

using namespace delta;

namespace {

TEST(WiredNetResolution, Wand_0_0) {
  auto r = ResolveWandWord({0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_1) {
  auto r = ResolveWandWord({0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_x) {
  auto r = ResolveWandWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_z) {
  auto r = ResolveWandWord({0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_0) {
  auto r = ResolveWandWord({1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_1) {
  auto r = ResolveWandWord({1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_x) {
  auto r = ResolveWandWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_1_z) {
  auto r = ResolveWandWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_0) {
  auto r = ResolveWandWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_1) {
  auto r = ResolveWandWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_x) {
  auto r = ResolveWandWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_z) {
  auto r = ResolveWandWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_0) {
  auto r = ResolveWandWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_1) {
  auto r = ResolveWandWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_x) {
  auto r = ResolveWandWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_z) {
  auto r = ResolveWandWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_0_0) {
  auto r = ResolveWorWord({0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_0_1) {
  auto r = ResolveWorWord({0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_0_x) {
  auto r = ResolveWorWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_0_z) {
  auto r = ResolveWorWord({0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_0) {
  auto r = ResolveWorWord({1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_1) {
  auto r = ResolveWorWord({1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_x) {
  auto r = ResolveWorWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_z) {
  auto r = ResolveWorWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_0) {
  auto r = ResolveWorWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_1) {
  auto r = ResolveWorWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_x) {
  auto r = ResolveWorWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_z) {
  auto r = ResolveWorWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_0) {
  auto r = ResolveWorWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_1) {
  auto r = ResolveWorWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_x) {
  auto r = ResolveWorWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_z) {
  auto r = ResolveWorWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetE2e, WorAnyDriverOneYieldsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WorAllZeroYieldsZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WandAnyDriverZeroYieldsZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WandAllOneYieldsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, PlainWireConflictIsX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'bx);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, TriorMatchesWorFunctionality) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  trior w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, TriandMatchesWandFunctionality) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  triand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WorHighZDriverYieldsToOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WorHighZDriverYieldsToZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WandHighZDriverYieldsToZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WandThreeDriversAnyZeroIsZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b1;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(WiredNetE2e, WorThreeDriversAnyOneIsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WorVectorResolvesPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor [3:0] w;\n"
                      "  logic [3:0] result;\n"
                      "  assign w = 4'b0011;\n"
                      "  assign w = 4'b0101;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x7u);
}

TEST(WiredNetE2e, WandVectorResolvesPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand [3:0] w;\n"
                      "  logic [3:0] result;\n"
                      "  assign w = 4'b1100;\n"
                      "  assign w = 4'b1010;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x8u);
}

TEST(WiredNetE2e, WorControllingOneOverridesXDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bx;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'b1);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WandControllingZeroOverridesXDriver) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bx;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'b0);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WorXWithNonControllingZeroIsX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bx;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'bx);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WorResolvesGatePrimitiveDrivers) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wor w;\n"
                      "  logic a, b;\n"
                      "  logic result;\n"
                      "  buf (w, a);\n"
                      "  buf (w, b);\n"
                      "  initial begin\n"
                      "    a = 1'b0;\n"
                      "    b = 1'b1;\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(WiredNetE2e, WandResolvesGatePrimitiveDrivers) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wand w;\n"
                      "  logic a, b;\n"
                      "  logic result;\n"
                      "  buf (w, a);\n"
                      "  buf (w, b);\n"
                      "  initial begin\n"
                      "    a = 1'b1;\n"
                      "    b = 1'b0;\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

}  // namespace
