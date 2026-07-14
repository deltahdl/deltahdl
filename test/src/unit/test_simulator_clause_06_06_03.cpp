#include <gtest/gtest.h>

#include "common/arena.h"
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

// --- Real-source, full-pipeline observation of §6.6.3 ---
//
// The per-word truth-table cases above pin the raw Table 6-3/6-4 combinators
// (ResolveWandWord/ResolveWorWord), which are pure single-stage functions. The
// property §6.6.3 actually defines, however, is about a *declared* wired net
// resolving *multiple drivers*: the resolution only fires once a wor/wand/
// trior/triand declaration meets more than one continuous assignment. These
// cases build the input the way real source does -- a wired-net declaration
// plus two or more continuous assignments -- and drive it through
// parse -> elaborate -> lower -> run, reading the resolved net back at time #1.
// The two continuous drivers are the constructs §6.6.3's rule consumes; on an
// ordinary wire the same 0/1 pair would resolve to x (see the contrast case),
// so a definite 1 or 0 here is exactly what the wired resolution buys.

// §6.6.3, C2 (Table 6-4): a wor net driven 0 and 1 resolves to 1 -- any driver
// at 1 pulls the wired-OR net to 1.
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

// §6.6.3 complement: a wor net with every driver at 0 stays 0, so the net is
// not merely stuck at 1.
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

// §6.6.3, C3 (Table 6-3): a wand net driven 1 and 0 resolves to 0 -- any driver
// at 0 pulls the wired-AND net to 0.
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

// §6.6.3 complement: a wand net with every driver at 1 stays 1, so the net is
// not merely stuck at 0.
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

// §6.6.3 contrast: the identical 0/1 driver pair on an ordinary wire conflicts
// to x. That the wor/wand cases above read a definite value -- and this one
// does not -- shows the resolution consults the declared net type, i.e. the
// wired truth tables are actually applied.
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

// §6.6.3, C4: "The net types wor and trior shall be identical [...] in
// functionality." Same 0/1 driver pair, declared trior, resolves to 1 exactly
// as the wor case does.
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

// §6.6.3, C5: "The net types wand and triand shall be identical [...] in
// functionality." Same 1/0 driver pair, declared triand, resolves to 0 exactly
// as the wand case does.
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

// §6.6.3 (Table 6-4, z column): a high-impedance driver yields to a defined
// driver on a wor net. 1 wor z is 1; the z contributes nothing.
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

// §6.6.3 (Table 6-4, z column): 0 wor z is 0 -- the z driver does not pull the
// wired-OR net up.
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

// §6.6.3 (Table 6-3, z column): 0 wand z is 0 on a wand net -- the defined 0
// driver decides and the z contributes nothing.
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

// §6.6.3, three drivers: "if any driver is 0, the value of the net is 0."
// Two drivers hold 1 and a third holds 0; the wand net resolves to 0.
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

// §6.6.3, three drivers: "when any of the drivers is 1, the resulting value of
// the net is 1." Two drivers hold 0 and a third holds 1; the wor net resolves
// to 1.
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

// §6.6.3 vector form: the wired truth table applies bit for bit across a vector
// net. wor [3:0] driven 4'b0011 and 4'b0101 resolves to 4'b0111.
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

// §6.6.3 vector form, wand side: wand [3:0] driven 4'b1100 and 4'b1010 resolves
// to 4'b1000, the bitwise wired-AND.
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

// §6.6.3 (Table 6-4, x column) input form: an x-valued driver, unlike a z one,
// is a genuine conflict -- but a controlling 1 still wins on a wor net. 1 wor x
// resolves to 1. Read back through ===1 so the case fails if the net were x.
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

// §6.6.3 (Table 6-3, x column) input form, wand side: a controlling 0 wins over
// an x-valued driver. 0 wand x resolves to 0.
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

// §6.6.3 (Table 6-4, x column) input form: with no controlling value present,
// an x driver against a non-controlling 0 leaves a wor net at x. 0 wor x is x
// -- the complement of the controlling-value case above.
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

// §6.6.3 driver-production input form: the drivers are Clause 28 gate
// primitives (two bufs) rather than continuous assignments -- the archetypal
// "wired logic configuration" the clause names. Two bufs driving a wor net with
// 0 and 1 resolve to 1, exactly as the wired-OR truth table requires. Building
// the drivers from real primitive syntax exercises the gate-instantiation path
// through parse -> elaborate -> lower -> run.
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

// §6.6.3 driver-production input form, wand side: two buf primitives driving a
// wand net with 1 and 0 resolve to 0, the wired-AND of the two gate outputs.
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
