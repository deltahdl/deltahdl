#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates and simulates a single three-state gate driving net `y` from data
// input `d` and control input `c`, then returns the settled 4-state value of
// `y` as a string ("0", "1", "x", or "z"). This drives the real production
// path: the elaborator lowering of the gate to a continuous assignment plus the
// simulator's expression evaluation and net resolution — not a reference model.
std::string DriveTristate(const char* gate, const char* data,
                          const char* ctrl) {
  SimFixture f;
  std::string src = std::string("module t;\n  wire y;\n  logic d, c;\n  ") +
                    gate + " g(y, d, c);\n  initial begin d = " + data +
                    "; c = " + ctrl + "; end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return "<elaborate-failed>";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  EXPECT_NE(var, nullptr);
  return var ? var->value.ToString() : "<no-output>";
}

// Drives `src` (data) and `ctrl` (control) of a gate per the supplied initial
// block body and returns the simulation time at which the output settled to its
// final value. The last scheduled transition is the gate output, so the final
// scheduler time reports the delay the production code applied to it.
uint64_t SettleTime(const std::string& decl, const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  logic src, ctrl;\n  " + decl +
                    "\n  initial begin " + stim + " end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.scheduler.CurrentTime().ticks;
}

// --- Table 28-5: unambiguous rows reproduced by production ---
//
// The rows where the control is a clean 0/1 are fully modelled by the lowered
// ternary. The ambiguous-control rows (L/H results) and a high-impedance data
// input passing through a conducting gate are strength-ambiguous behaviour that
// the LRM defers to 28.12.2; production renders them functionally and they are
// not asserted here.

TEST(TristateGateSim, Bufif1ConductsWhenControlHigh) {
  // bufif1 conducts when control is 1, passing the data value.
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'b1"), "0");
  EXPECT_EQ(DriveTristate("bufif1", "1'b1", "1'b1"), "1");
  EXPECT_EQ(DriveTristate("bufif1", "1'bx", "1'b1"), "x");
}

TEST(TristateGateSim, Bufif1HighImpedanceWhenControlLow) {
  // Control 0 turns the driver off: the output floats to z regardless of data.
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif1", "1'b1", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif1", "1'bx", "1'b0"), "z");
}

TEST(TristateGateSim, Bufif0ConductsWhenControlLow) {
  // bufif0 conducts when control is 0.
  EXPECT_EQ(DriveTristate("bufif0", "1'b0", "1'b0"), "0");
  EXPECT_EQ(DriveTristate("bufif0", "1'b1", "1'b0"), "1");
  EXPECT_EQ(DriveTristate("bufif0", "1'bx", "1'b0"), "x");
}

TEST(TristateGateSim, Bufif0HighImpedanceWhenControlHigh) {
  EXPECT_EQ(DriveTristate("bufif0", "1'b0", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'b1", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'bx", "1'b1"), "z");
}

TEST(TristateGateSim, Notif1ConductsAndInvertsWhenControlHigh) {
  // notif1 conducts when control is 1 and inverts the data.
  EXPECT_EQ(DriveTristate("notif1", "1'b0", "1'b1"), "1");
  EXPECT_EQ(DriveTristate("notif1", "1'b1", "1'b1"), "0");
  EXPECT_EQ(DriveTristate("notif1", "1'bx", "1'b1"), "x");
}

TEST(TristateGateSim, Notif1HighImpedanceWhenControlLow) {
  EXPECT_EQ(DriveTristate("notif1", "1'b0", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("notif1", "1'b1", "1'b0"), "z");
}

TEST(TristateGateSim, Notif0ConductsAndInvertsWhenControlLow) {
  // notif0 conducts when control is 0 and inverts the data.
  EXPECT_EQ(DriveTristate("notif0", "1'b0", "1'b0"), "1");
  EXPECT_EQ(DriveTristate("notif0", "1'b1", "1'b0"), "0");
  EXPECT_EQ(DriveTristate("notif0", "1'bx", "1'b0"), "x");
}

TEST(TristateGateSim, Notif0HighImpedanceWhenControlHigh) {
  EXPECT_EQ(DriveTristate("notif0", "1'b0", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("notif0", "1'b1", "1'b1"), "z");
}

TEST(TristateGateSim, GateCanDriveHighImpedance) {
  // The defining property of these gates: in addition to 0 and 1 they can put
  // the output into the high-impedance state.
  EXPECT_EQ(DriveTristate("bufif1", "1'b1", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("notif0", "1'b0", "1'b1"), "z");
}

// --- Delay specification (Table 28-5 narrative) ---
//
// The instance carries up to three delays. The first is the rise delay, the
// second the fall delay, the third the delay of a transition to z, and the
// smallest of the supplied delays governs a transition to x.

TEST(TristateGateSim, RiseDelayGovernsZeroToOne) {
  // Conducting bufif1; data climbs 0 -> 1 at t=20, output rises 5 later.
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, FallDelayGovernsOneToZero) {
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

TEST(TristateGateSim, TurnOffDelayGovernsTransitionToZ) {
  // Dropping control turns the driver off; the third delay times the move to z.
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 35u);
}

TEST(TristateGateSim, SmallestDelayGovernsTransitionToX) {
  // Data goes unknown while conducting; the smallest of the three delays (the
  // 20 in the third slot) times the move to x, not the 40 rise delay.
  uint64_t t = SettleTime("bufif1 #(40, 30, 20) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #50 src = 1'bx;");
  EXPECT_EQ(t, 70u);
}

TEST(TristateGateSim, TwoDelayFormUsesSmallerForTurnOff) {
  // With two delays and no explicit turn-off delay, the smaller of the two
  // applies to the transition to z.
  uint64_t t = SettleTime("bufif1 #(5, 10) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, SingleDelayAppliesToEveryTransition) {
  // One delay governs the rise at t=20 and the fall at t=40 alike, so the final
  // transition settles 7 after it is stimulated.
  uint64_t t = SettleTime("bufif1 #7 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1; "
                          "#20 src = 1'b0;");
  EXPECT_EQ(t, 47u);
}

TEST(TristateGateSim, NoDelaySpecificationPropagatesImmediately) {
  // Without a delay specification the output tracks its input with no delay, so
  // it settles at the very time the input changes.
  uint64_t t = SettleTime("bufif1 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 20u);
}

}  // namespace
