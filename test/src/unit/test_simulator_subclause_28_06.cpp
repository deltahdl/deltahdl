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

// --- Table 28-5: the rows reproduced by production ---
//
// The rows where the control is a clean 0/1 are fully modelled by the lowered
// ternary. The control x/z columns give L and H, which §28.6 defines as values
// -- "The symbol L shall represent a result that has a value 0 or z. The symbol
// H shall represent a result that has a value 1 or z" -- and §28.12.2 draws as
// a strength: a range on one side of the scale, from the gate's own drive level
// down to high impedance. The value such a gate settles on is x either way, so
// the cases at the end of this file read the strength back with %v, which is
// where L and H are told from an unambiguous x. A high-impedance data value on
// a conducting gate is not one of those rows: Table 28-5 gives it a definite x,
// which is asserted below.

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

TEST(TristateGateSim, ConductingGateFoldsHighImpedanceDataToX) {
  // Table 28-5: a z on the data input cannot be transmitted, so a conducting
  // gate drives x -- a definite x (not an L/H strength-ambiguous result, which
  // arises only from an unknown control). The inverting notif variants map z to
  // x just as the non-inverting bufif variants do.
  EXPECT_EQ(DriveTristate("bufif1", "1'bz", "1'b1"), "x");
  EXPECT_EQ(DriveTristate("bufif0", "1'bz", "1'b0"), "x");
  EXPECT_EQ(DriveTristate("notif1", "1'bz", "1'b1"), "x");
  EXPECT_EQ(DriveTristate("notif0", "1'bz", "1'b0"), "x");
}

TEST(TristateGateSim, BlockedGateStillFloatsWithHighImpedanceData) {
  // When the gate is off the data value is irrelevant: the output floats to z
  // even if the data input is itself high-impedance.
  EXPECT_EQ(DriveTristate("bufif1", "1'bz", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'bz", "1'b1"), "z");
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

TEST(TristateGateSim, TwoDelayFormUsesSmallerForTransitionToX) {
  // The two-delay form carries no dedicated x delay, so a move to x takes the
  // smaller of the two supplied delays -- the same delay it applies to a
  // transition to z. Data goes unknown at t=50 on a conducting gate, so the
  // output settles 5 (the smaller of 5 and 10) later.
  uint64_t t = SettleTime("bufif1 #(5, 10) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #50 src = 1'bx;");
  EXPECT_EQ(t, 55u);
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

TEST(TristateGateSim, SingleDelayAlsoTimesTurnOff) {
  // "All output transitions" includes a turn-off: with a lone delay, dropping
  // the control at t=20 moves the output to z 7 later, the same delay a data
  // change would take.
  uint64_t t = SettleTime("bufif1 #7 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 27u);
}

// --- Delay values are constant expressions (literal covered above; here a
// parameter and a localparam, which reach the delay through the expression
// evaluator rather than as an immediate literal). ---

TEST(TristateGateSim, RiseDelayFromParameterGovernsTransition) {
  // A parameter in the rise slot is resolved to its value and drives the same
  // rise-delay mapping a literal would: with P = 5, a 0 -> 1 climb at t=20
  // settles at t=25.
  uint64_t t =
      SettleTime("parameter P = 5;\n  bufif1 #(P, 10, 15) g(y, src, ctrl);",
                 "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, FallDelayFromLocalparamGovernsTransition) {
  // A localparam takes the same constant-expression path in the fall slot: with
  // Q = 10, a 1 -> 0 drop at t=20 settles at t=30.
  uint64_t t =
      SettleTime("localparam Q = 10;\n  bufif1 #(5, Q, 15) g(y, src, ctrl);",
                 "ctrl = 1'b1; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

// The strength one three-state gate drives, read back through §21.2.1.4's %v.
// The gate's own drive strength is what it drives at, so the source names none
// and takes the strong default of §28.11.
std::string DriveTristateStrength(const std::string& decl,
                                  const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  " + decl + "\n  initial begin " +
                    stim + " #1 $display(\"%v\", y); end\nendmodule\n";
  return RunCapture(src, f);
}

// §28.6 Table 28-5, bufif1 with a control of x and a data value of 1: the gate
// drives H, "a result that has a value 1 or z", which §28.12.2's Figure 28-6
// draws as the output of exactly this gate and Figure 28-7 as a range on the
// strength1 side running from the driving level down to high impedance.
// §21.2.1.4 renders that range as the level's mnemonic and the letter H: StH.
//
// The gate drove an unambiguous x instead -- the conditional it lowers to
// combines the data value with high impedance and yields x, and a driver of
// value x put its own level on both sides of the scale -- so %v printed StX and
// the two logic values Table 21-3 defines for an ambiguous value were
// unreachable from any source.
TEST(TristateGateSim, Bufif1WithUnknownControlDrivesStrongH) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  bufif1 g(y, d, c);",
                                  "d = 1'b1; c = 1'bx;"),
            "StH\n");
}

// Figure 28-6's other gate: a bufif0 whose data input is driven weak and whose
// control is x drives StL. The figure draws We0 in and StL out, so the case
// says the ambiguity is the gate's own and the level is the gate's own -- an
// output taking its input's strength would print WeL.
TEST(TristateGateSim, Bufif0WithUnknownControlDrivesStrongLFromAWeakInput) {
  EXPECT_EQ(DriveTristateStrength(
                "wire d;\n  logic c;\n"
                "  assign (weak0, weak1) d = 1'b0;\n  bufif0 g(y, d, c);",
                "c = 1'bx;"),
            "StL\n");
}

// The value beside the strength. Table 28-5 leaves the control x column at L
// for a data value of 0, and L is 0 or z rather than either of them, so the net
// reads x: a design cannot take the ambiguity for a driven 0.
TEST(TristateGateSim, Bufif1WithUnknownControlReadsAsUnknown) {
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'bx"), "x");
}

// The notif rows of the same column, where the inversion decides which of the
// two the gate drives: notif1 with a control of x and a data value of 0 gives
// H, the row Table 28-5 writes as "0 z 1 H H". A gate reading its data terminal
// rather than the value it transmits would drive L here.
TEST(TristateGateSim, Notif1WithUnknownControlDrivesTheInvertedSide) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  notif1 g(y, d, c);",
                                  "d = 1'b0; c = 1'bx;"),
            "StH\n");
}

// §28.6's control z column answers as the x column does -- Table 28-5 gives the
// two the same L and H -- so a control left floating drives the same range.
TEST(TristateGateSim, Bufif1WithHighImpedanceControlDrivesStrongH) {
  EXPECT_EQ(DriveTristateStrength("logic d;\n  wire c;\n  bufif1 g(y, d, c);",
                                  "d = 1'b1;"),
            "StH\n");
}

// §28.12.3 with the range this gate makes: Figure 28-23 combines an ambiguous
// signal occupying one side with a weaker unambiguous driver of the other
// value, and its result runs from the weaker driver's level through high
// impedance to the ambiguous signal's own. §21.2.1.4 renders two sides whose
// strongest levels differ with the two-digit form, so a strong H against a pull
// 0 prints 56X.
TEST(TristateGateSim, StrongHAgainstAWeakerZeroRendersTheTwoDigitForm) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  bufif1 g(y, d, c);\n"
                                  "  assign (pull0, pull1) y = 1'b0;",
                                  "d = 1'b1; c = 1'bx;"),
            "56X\n");
}

}  // namespace
