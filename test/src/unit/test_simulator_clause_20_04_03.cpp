#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

Expr* MkTimeformatCall(Arena& arena, int64_t units, int64_t precision,
                       std::string_view suffix, int64_t width) {
  return MkSysCall(
      arena, "$timeformat",
      {MkInt(arena, static_cast<uint64_t>(units)),
       MkInt(arena, static_cast<uint64_t>(precision)), MkStr(arena, suffix),
       MkInt(arena, static_cast<uint64_t>(width))});
}

// Table 20-3 lists default values for $timeformat's arguments. With no call
// yet executed, the configured precision, suffix, and minimum field width
// shall match those defaults.
TEST(TimeformatSysTask, DefaultPrecisionSuffixAndFieldWidth) {
  SysTaskFixture f;
  const auto& spec = f.ctx.GetTimeFormat();
  EXPECT_EQ(spec.precision_number, 0);
  EXPECT_TRUE(spec.suffix_string.empty());
  EXPECT_EQ(spec.minimum_field_width, 20);
}

// Per Table 20-3, the default units_number is the smallest time precision
// argument of all `timescale directives in the design; this simulator models
// that quantity as the global precision configured on SimContext.
TEST(TimeformatSysTask, DefaultUnitsFollowsGlobalPrecision) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kFs);
  EXPECT_EQ(f.ctx.GetTimeFormat().units_number, -15);
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  EXPECT_EQ(f.ctx.GetTimeFormat().units_number, -9);
}

// Invoking $timeformat shall install the supplied units number, precision
// number, suffix string, and minimum field width.
TEST(TimeformatSysTask, InvocationInstallsAllFourArguments) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, -9, 3, " ns", 12), f.ctx, f.arena);
  const auto& spec = f.ctx.GetTimeFormat();
  EXPECT_EQ(spec.units_number, -9);
  EXPECT_EQ(spec.precision_number, 3);
  EXPECT_EQ(spec.suffix_string, " ns");
  EXPECT_EQ(spec.minimum_field_width, 12);
}

// The configured values persist until another $timeformat is invoked, at
// which point the new arguments replace them.
TEST(TimeformatSysTask, SecondInvocationOverridesFirst) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, -9, 1, " ns", 5), f.ctx, f.arena);
  EvalExpr(MkTimeformatCall(f.arena, -12, 2, " ps", 8), f.ctx, f.arena);
  const auto& spec = f.ctx.GetTimeFormat();
  EXPECT_EQ(spec.units_number, -12);
  EXPECT_EQ(spec.precision_number, 2);
  EXPECT_EQ(spec.suffix_string, " ps");
  EXPECT_EQ(spec.minimum_field_width, 8);
}

// Shall: units_number is an integer in the Table 20-2 range from 2 to -15.
// A value outside that range is reported as an error and the existing
// configuration is left untouched.
TEST(TimeformatSysTask, UnitsAboveRangeRaisesDiagnostic) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, 3, 0, "", 20), f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TimeformatSysTask, UnitsBelowRangeRaisesDiagnostic) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, -16, 0, "", 20), f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Shall: precision_number is an integer in the Table 20-2 range from 2 to
// -15. Out-of-range precision values are likewise rejected.
TEST(TimeformatSysTask, PrecisionOutsideRangeRaisesDiagnostic) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, -9, -16, "", 20), f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

// $timeformat specifies how %t reports time in the display tasks of 21.2:
// after the installation the formatted output carries the configured suffix
// string and is padded to the minimum field width.
TEST(TimeformatSysTask, PercentTUsesConfiguredSuffixAndFieldWidth) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  EvalExpr(MkTimeformatCall(f.arena, -9, 0, " ns", 12), f.ctx, f.arena);
  Logic4Vec v = MakeLogic4VecVal(f.arena, 64, 7);
  std::string out =
      FormatDisplay("%t", {v}, {.time_format = &f.ctx.GetTimeFormat()});
  EXPECT_GE(out.size(), 12u);
  EXPECT_NE(out.find(" ns"), std::string::npos);
}

// The Table 20-2 range is closed; the endpoint values 2 and -15 are valid
// inputs and shall not raise a diagnostic.
TEST(TimeformatSysTask, RangeEndpointsAreAccepted) {
  SysTaskFixture f;
  EvalExpr(MkTimeformatCall(f.arena, 2, -15, "", 0), f.ctx, f.arena);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The configured time unit persists "until another $timeformat ... is
// invoked", so unrelated changes to the global precision after an explicit
// invocation must not disturb the previously installed units_number.
TEST(TimeformatSysTask, ExplicitUnitsAreShieldedFromPrecisionChange) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  EvalExpr(MkTimeformatCall(f.arena, -9, 0, "", 0), f.ctx, f.arena);
  f.ctx.SetGlobalPrecision(TimeUnit::kFs);
  EXPECT_EQ(f.ctx.GetTimeFormat().units_number, -9);
}

// $timeformat sets the time unit, so the same raw tick count formats
// differently after a re-invocation that selects a different unit and
// precision combination.
TEST(TimeformatSysTask, PercentTScalesTicksToConfiguredUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  EvalExpr(MkTimeformatCall(f.arena, -9, 2, "", 0), f.ctx, f.arena);
  Logic4Vec v = MakeLogic4VecVal(f.arena, 64, 42);
  std::string out =
      FormatDisplay("%t", {v}, {.time_format = &f.ctx.GetTimeFormat()});
  EXPECT_NE(out.find("42.00"), std::string::npos);
}

}  // namespace
