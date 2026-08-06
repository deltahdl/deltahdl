#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_scheduler.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Logic4Word ResolveTwoBit(Arena& arena, NetType type, Logic4Word a,
                                Logic4Word b) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = type;
  net.resolved = var;
  auto da = MakeLogic4Vec(arena, 1);
  da.words[0] = a;
  auto db = MakeLogic4Vec(arena, 1);
  db.words[0] = b;
  net.drivers.push_back(da);
  net.drivers.push_back(db);
  net.Resolve(arena);
  return {var->value.words[0].aval & 1, var->value.words[0].bval & 1};
}

TEST(Tri0Tri1Resolution, Tri0_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_1_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_1_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_1_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_1_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0DrivenValuePassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(Tri0Tri1Resolution, Tri1DrivenValuePassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xCD));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// §6.6.5: with no driver connected, a tri0 net settles to 0 carrying pull
// strength (the implicit resistive pulldown), not the default high-impedance.
TEST(Tri0Tri1Resolution, Tri0UndrivenDefaultsToZeroWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // No drivers connected to the net.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
}

// §6.6.5: with no driver connected, a tri1 net settles to 1 carrying pull
// strength (the implicit resistive pullup).
TEST(Tri0Tri1Resolution, Tri1UndrivenDefaultsToOneWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // No drivers connected to the net.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
}

// §6.6.5: a tri0 net is equivalent to a wire driven by a continuous 0 of pull
// strength. Within one vector, an actual driver wins on the bits it drives,
// while every bit it leaves at z falls to the pulldown value 0. Exercises the
// per-bit residual-z fixup across a multi-bit net (low nibble driven, high
// nibble left floating).
TEST(Tri0Tri1Resolution, Tri0PullsOnlyResidualZBitsLowAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // Bits 0-3 drive 1,0,1,0; bits 4-7 are z (aval&bval both set).
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05,
                  0xF0};  // low nibble driven; high nibble z=(aval0,bval1)
  net.drivers.push_back(drv);
  net.Resolve(arena);
  // Driven bits pass through unchanged; floating bits pull down to 0.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x05u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

// §6.6.5: a tri1 net is equivalent to a wire driven by a continuous 1 of pull
// strength. The driven bits pass through; the floating bits pull up to 1.
TEST(Tri0Tri1Resolution, Tri1PullsOnlyResidualZBitsHighAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // Bits 0-3 drive 1,0,1,0; bits 4-7 are z.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05,
                  0xF0};  // low nibble driven; high nibble z=(aval0,bval1)
  net.drivers.push_back(drv);
  net.Resolve(arena);
  // Driven bits pass through unchanged; floating bits pull up to 1.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xF5u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

// --- Real-source, full-pipeline observation of §6.6.5 ---
//
// The synthetic cases above pin Net::Resolve against Table 6-5/6-6 by handing
// it drivers directly. The behavior §6.6.5 actually defines, though, is about a
// declared tri0/tri1 net that *collects* drivers from real source: the net
// carries an implicit continuous 0 (tri0) or 1 (tri1) of pull strength, and the
// resolved value is that pull source combined with whatever continuous
// assignments drive the net. So the input is built the way real source builds
// it -- a tri0/tri1 declaration plus continuous assignments (consuming §6.6.1's
// net/assign machinery and §28.11's drive-strength syntax) -- and driven
// through parse -> elaborate -> lower -> run, reading the resolved net back.

// §6.6.5: the distinguishing property -- an undriven tri0 does not merely read
// back as 0 through a value cast (high-impedance would too), it settles to a
// *known* 0. Case equality (===) tells the two apart: z === 1'b0 is false, so a
// result of 1 confirms the net holds a real 0, the pulldown value.
TEST(Tri0Tri1ResolutionE2e, Tri0UndrivenIsKnownZeroNotHighZ) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'b0);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: an undriven tri1 net settles to 1 (its resistive pullup).
TEST(Tri0Tri1ResolutionE2e, Tri1UndrivenReadsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: a high-impedance driver contributes nothing, so the implicit pulldown
// still determines the value -- a tri0 driven only by z reads 0.
TEST(Tri0Tri1ResolutionE2e, Tri0HighZDriverPullsToZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §6.6.5: the mirror on tri1 -- a lone high-impedance driver leaves the pullup
// in charge, so the net reads 1.
TEST(Tri0Tri1ResolutionE2e, Tri1HighZDriverPullsToOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: an actual driver of strong strength overrides the pull. A strong 1 on
// a tri0 wins over the implicit pulldown 0, so the net reads 1.
TEST(Tri0Tri1ResolutionE2e, Tri0StrongDriverOverridesPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: a strong 0 on a tri1 overrides the implicit pullup 1, so the net
// reads 0.
TEST(Tri0Tri1ResolutionE2e, Tri1StrongZeroDriverOverridesPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §6.6.5 consuming §28.11: the implicit pull combines with the drivers by
// strength, so a driver *weaker* than pull loses. A weak 1 on a tri0 is
// overridden by the implicit pull-strength 0, and the net reads 0 -- the case
// Table 6-5 (stated only for strong drivers) does not cover.
TEST(Tri0Tri1ResolutionE2e, Tri0WeakDriverLosesToPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign (weak1, weak0) w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §6.6.5 consuming §28.11: mirror on tri1 -- a weak 0 loses to the implicit
// pull-strength 1, so the net reads 1.
TEST(Tri0Tri1ResolutionE2e, Tri1WeakDriverLosesToPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign (weak1, weak0) w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5 consuming §28.11: a driver of exactly pull strength ties with the
// implicit pull source. A pull 1 against the implicit pull 0 on a tri0 is an
// equal-strength conflict, so the net resolves to x.
TEST(Tri0Tri1ResolutionE2e, Tri0EqualPullDriverConflictsToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign (pull1, pull0) w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5 consuming §28.11: the tri1 counterpart, where the implicit pull holds
// the opposite value. A pull-strength 0 driver drives pull on the 0 side, which
// contends with tri1's implicit pull 1 -- equal strength, opposing value -- so
// the net resolves to x. (The same 1'b0 driver on a tri0 would instead AGREE
// with the implicit pull 0, which is why this case is specific to tri1.)
TEST(Tri0Tri1ResolutionE2e, Tri1EqualPullDriverConflictsToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign (pull1, pull0) w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: the pull acts bit by bit across a vector. On a 4-bit tri0 a driver of
// 4'bzz01 drives bits 0-1 and floats bits 2-3; the floating bits fall to the
// pulldown 0, so the net resolves to 4'b0001.
TEST(Tri0Tri1ResolutionE2e, Tri0VectorResidualZPullsPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 [3:0] w;\n"
                      "  logic result;\n"
                      "  assign w = 4'bzz01;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 4'b0001);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5: mirror across a vector tri1 -- the floating high bits pull up to 1,
// so 4'bzz01 resolves to 4'b1101.
TEST(Tri0Tri1ResolutionE2e, Tri1VectorResidualZPullsPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 [3:0] w;\n"
                      "  logic result;\n"
                      "  assign w = 4'bzz01;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 4'b1101);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.6.5 / Table 6-5: two strong drivers of opposing value on a tri0 conflict
// (the resulting strength is strong, but the value is x) -- the pull does not
// break the tie because both real drivers outrank it.
TEST(Tri0Tri1ResolutionE2e, Tri0ConflictingStrongDriversResolveToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

}  // namespace
