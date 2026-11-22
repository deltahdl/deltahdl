#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kActionsDesign =
    "module m(input logic clk);\n"
    "  logic a = 1, v = 0;\n"
    "  int pn = 0, pv = 0, fl = 0, mf = 0, mn = 0, mv = 0;\n"
    "  an: assert property (@(posedge clk) a) pn += $time;\n"
    "  av: assert property (@(posedge clk) v |-> a) pv += $time;\n"
    "  af: assert property (@(posedge clk) v) else fl += $time;\n"
    "  amf: assert property (@(posedge clk) 1 ##1 v) else mf += $time;\n"
    "  amn: assert property (@(posedge clk) 1 ##2 a) mn += $time;\n"
    "  amv: assert property (@(posedge clk) 1 ##2 v |-> a) mv += $time;\n"
    "endmodule\n"
    "module top;\n"
    "  logic clk = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  m u1(clk);\n"
    "  m u2(clk);\n"
    "  initial begin #10 $arm; #10 $arm; #10 $arm; #10 $finish; end\n"
    "endmodule\n";

constexpr const char* kU1 = "top.u1";
constexpr const char* kU2 = "top.u2";

struct Counts {
  int pn = 0;
  int pv = 0;
  int fl = 0;
  int mf = 0;
  int mn = 0;
  int mv = 0;
};

constexpr Counts kUncontrolled = {80, 80, 80, 75, 60, 60};
constexpr Counts kOffFromTheFirstArm = {5, 5, 5, 15, 25, 25};
constexpr Counts kOffUntilTheSecondArm = {65, 65, 65, 50, 25, 25};
constexpr Counts kKilledUntilTheSecondArm = {65, 65, 65, 35, 0, 0};
constexpr Counts kEndedAtTheFirstArm = {5, 5, 5, 0, 0, 0};
constexpr Counts kOffFromTheSecondArm = {20, 20, 20, 40, 60, 60};
constexpr Counts kVacuousOffFromTheFirstArm = {80, 5, 80, 75, 60, 25};
constexpr Counts kActionsOffUntilTheSecondArm = {65, 65, 65, 50, 25, 25};

struct Op {
  int arm = 0;
  int operation = 0;
  const char* target = nullptr;
  int result = 1;
};

struct ControlRun {
  const char* name;
  std::vector<Op> ops;
  Counts u1;
  Counts u2;
  std::vector<uint64_t> u1_failures;
};

ControlRun Everywhere(const char* name, std::vector<Op> ops, Counts counts,
                      std::vector<uint64_t> u1_failures) {
  return {name, std::move(ops), counts, counts, std::move(u1_failures)};
}

void Apply(const Op& op) {
  vpiHandle handle = op.target == nullptr
                         ? nullptr
                         : vpi_handle_by_name(VpiText(op.target), nullptr);
  EXPECT_EQ(vpi_control(op.operation, handle), op.result)
      << "operation " << op.operation << " at arm " << op.arm;
}

Counts CountsOf(const std::string& instance) {
  Counts counts;
  for (auto [field, name] :
       {std::pair{&Counts::pn, "pn"}, std::pair{&Counts::pv, "pv"},
        std::pair{&Counts::fl, "fl"}, std::pair{&Counts::mf, "mf"},
        std::pair{&Counts::mn, "mn"}, std::pair{&Counts::mv, "mv"}}) {
    counts.*field = IntOf((instance + "." + name).c_str());
  }
  return counts;
}

std::array<int, 3> Settled(const Counts& c) { return {c.pn, c.pv, c.fl}; }

std::array<int, 3> InFlight(const Counts& c) { return {c.mf, c.mn, c.mv}; }

class SystemControlRun : public AssertionRun,
                         public ::testing::WithParamInterface<ControlRun> {
 protected:
  void RunRow() {
    const ControlRun* row = &GetParam();
    std::vector<std::function<void()>> steps;
    steps.reserve(3);
    for (int arm = 1; arm <= 3; ++arm) {
      steps.emplace_back([row, arm] {
        if (arm == 1) {
          ASSERT_NE(WatchAssertion("top.u1.af", cbAssertionFailure), nullptr);
        }
        for (const Op& op : row->ops) {
          if (op.arm == arm) Apply(op);
        }
      });
    }
    ArmInTurn(std::move(steps));
    Run(kActionsDesign);
  }
};

TEST_P(SystemControlRun, ControlsActOnTheirScopeFromTheirTimeOn) {
  RunRow();
  EXPECT_EQ(Settled(CountsOf(kU1)), Settled(GetParam().u1));
  EXPECT_EQ(Settled(CountsOf(kU2)), Settled(GetParam().u2));
  std::vector<uint64_t> failures;
  for (const AssertionCall& call : CallsOf(cbAssertionFailure)) {
    failures.push_back(call.cb_time);
  }
  EXPECT_EQ(failures, GetParam().u1_failures);
}

class InFlightControlRun : public SystemControlRun {};

TEST_P(InFlightControlRun, AnAttemptInFlightMeetsOnlyTheControlsThatDiscard) {
  RunRow();
  EXPECT_EQ(InFlight(CountsOf(kU1)), InFlight(GetParam().u1));
  EXPECT_EQ(InFlight(CountsOf(kU2)), InFlight(GetParam().u2));
}

std::vector<uint64_t> EveryFailure() { return {15, 25, 35}; }

std::vector<ControlRun> StateControls() {
  return {
      Everywhere("NoControl", {}, kUncontrolled, EveryFailure()),
      Everywhere("OffThenOn", {{1, vpiAssertionSysOff}, {2, vpiAssertionSysOn}},
                 kOffUntilTheSecondArm, {25, 35}),
      Everywhere("KillThenOn",
                 {{1, vpiAssertionSysKill}, {2, vpiAssertionSysOn}},
                 kKilledUntilTheSecondArm, {25, 35}),
      Everywhere("OffThenReset",
                 {{1, vpiAssertionSysOff}, {2, vpiAssertionSysReset}},
                 {65, 65, 65, 50, 0, 0}, {25, 35}),
      Everywhere("AssertionDisabledThenReset",
                 {{1, vpiAssertionDisable, "top.u1.af"},
                  {1, vpiAssertionDisable, "top.u2.af"},
                  {2, vpiAssertionSysReset}},
                 {80, 80, 65, 50, 0, 0}, {25, 35}),
      Everywhere("End", {{1, vpiAssertionSysEnd}}, kEndedAtTheFirstArm, {}),
      Everywhere("LockRefusesKillResetAndEnd",
                 {{1, vpiAssertionSysLock},
                  {1, vpiAssertionSysKill, nullptr, 0},
                  {1, vpiAssertionSysReset, nullptr, 0},
                  {1, vpiAssertionSysEnd, nullptr, 0}},
                 kUncontrolled, EveryFailure()),
      Everywhere("LockRefusesOnUntilUnlock",
                 {{1, vpiAssertionSysOff},
                  {2, vpiAssertionSysLock},
                  {2, vpiAssertionSysOn, nullptr, 0},
                  {3, vpiAssertionSysUnlock},
                  {3, vpiAssertionSysOn}},
                 {40, 40, 40, 15, 25, 25}, {35}),
      Everywhere("LockRefusesOffUntilUnlock",
                 {{1, vpiAssertionSysLock},
                  {1, vpiAssertionSysOff, nullptr, 0},
                  {2, vpiAssertionSysUnlock},
                  {2, vpiAssertionSysOff}},
                 kOffFromTheSecondArm, {15}),
      ControlRun{"ScopedKillThenOn",
                 {{1, vpiAssertionSysKill, kU1}, {2, vpiAssertionSysOn, kU1}},
                 kKilledUntilTheSecondArm,
                 kUncontrolled,
                 {25, 35}},
      ControlRun{"ScopedReset",
                 {{1, vpiAssertionSysReset, kU1}},
                 {80, 80, 80, 60, 35, 35},
                 kUncontrolled,
                 EveryFailure()},
      ControlRun{"ScopedEnd",
                 {{1, vpiAssertionSysEnd, kU1}},
                 kEndedAtTheFirstArm,
                 kUncontrolled,
                 {}},
      ControlRun{"ScopedOn",
                 {{1, vpiAssertionSysOff}, {2, vpiAssertionSysOn, kU1}},
                 kOffUntilTheSecondArm,
                 kOffFromTheFirstArm,
                 {25, 35}}};
}

std::vector<ControlRun> ActionControls() {
  return {
      Everywhere("PassActionOffThenOn",
                 {{1, vpiAssertionSysDisablePassAction},
                  {2, vpiAssertionSysEnablePassAction}},
                 {65, 65, 80, 75, 25, 25}, EveryFailure()),
      Everywhere("PassActionOffTwiceThenOnOnce",
                 {{1, vpiAssertionSysDisablePassAction},
                  {2, vpiAssertionSysDisablePassAction},
                  {3, vpiAssertionSysEnablePassAction}},
                 {40, 40, 80, 75, 25, 25}, EveryFailure()),
      Everywhere("PassActionOnWhileOn",
                 {{1, vpiAssertionSysEnablePassAction},
                  {2, vpiAssertionSysDisablePassAction},
                  {3, vpiAssertionSysEnablePassAction}},
                 {55, 55, 80, 75, 60, 60}, EveryFailure()),
      Everywhere("VacuousActionOff", {{1, vpiAssertionSysDisableVacuousAction}},
                 kVacuousOffFromTheFirstArm, EveryFailure()),
      Everywhere("PassActionOffThenNonvacuousOn",
                 {{1, vpiAssertionSysDisablePassAction},
                  {2, vpiAssertionSysEnableNonvacuousAction}},
                 {65, 5, 80, 75, 25, 25}, EveryFailure()),
      Everywhere("VacuousActionOffTwiceThenPassOn",
                 {{1, vpiAssertionSysDisableVacuousAction},
                  {2, vpiAssertionSysDisableVacuousAction},
                  {3, vpiAssertionSysEnablePassAction}},
                 {80, 40, 80, 75, 60, 25}, EveryFailure()),
      Everywhere("NonvacuousActionOnTwice",
                 {{1, vpiAssertionSysDisablePassAction},
                  {2, vpiAssertionSysEnableNonvacuousAction},
                  {3, vpiAssertionSysEnableNonvacuousAction}},
                 {65, 5, 80, 75, 25, 25}, EveryFailure()),
      Everywhere("FailActionOffTwiceThenOnOnce",
                 {{1, vpiAssertionSysDisableFailAction},
                  {2, vpiAssertionSysDisableFailAction},
                  {3, vpiAssertionSysEnableFailAction}},
                 {80, 80, 40, 15, 60, 60}, EveryFailure()),
      Everywhere("FailActionOnWhileOn",
                 {{1, vpiAssertionSysEnableFailAction},
                  {2, vpiAssertionSysDisableFailAction},
                  {3, vpiAssertionSysEnableFailAction}},
                 {80, 80, 55, 40, 60, 60}, EveryFailure()),
      Everywhere("ActionsOffThenReset",
                 {{1, vpiAssertionSysDisablePassAction},
                  {2, vpiAssertionSysDisableFailAction},
                  {3, vpiAssertionSysReset}},
                 {40, 40, 55, 40, 25, 25}, EveryFailure()),
      Everywhere("LockRefusesFailActionAndDisableUntilUnlock",
                 {{1, vpiAssertionSysLock},
                  {1, vpiAssertionSysDisableFailAction, nullptr, 0},
                  {1, vpiAssertionDisable, "top.u1.af", 0},
                  {2, vpiAssertionSysUnlock},
                  {2, vpiAssertionSysDisableFailAction}},
                 {80, 80, 20, 40, 60, 60}, EveryFailure()),
      ControlRun{"ScopedPassAndFailActions",
                 {{1, vpiAssertionSysDisablePassAction, kU1},
                  {1, vpiAssertionSysDisableFailAction, kU1},
                  {2, vpiAssertionSysEnablePassAction, kU1},
                  {2, vpiAssertionSysEnableFailAction, kU1}},
                 kActionsOffUntilTheSecondArm,
                 kUncontrolled,
                 EveryFailure()},
      ControlRun{"ScopedVacuousAndNonvacuousActions",
                 {{1, vpiAssertionSysDisableVacuousAction, kU1},
                  {2, vpiAssertionSysDisablePassAction, kU2},
                  {3, vpiAssertionSysEnableNonvacuousAction, kU2}},
                 kVacuousOffFromTheFirstArm,
                 {55, 20, 80, 75, 60, 60},
                 EveryFailure()}};
}

ControlRun ScopedLock() {
  return ControlRun{"ScopedLock",
                    {{1, vpiAssertionSysLock, kU1},
                     {1, vpiAssertionSysOff, kU1, 0},
                     {1, vpiAssertionSysOff, kU2},
                     {2, vpiAssertionSysUnlock, kU1},
                     {2, vpiAssertionSysOff, kU1}},
                    kOffFromTheSecondArm,
                    kOffFromTheFirstArm,
                    {15}};
}

std::string RowName(const ::testing::TestParamInfo<ControlRun>& info) {
  return info.param.name;
}

INSTANTIATE_TEST_SUITE_P(StateControls, SystemControlRun,
                         ::testing::ValuesIn(StateControls()), RowName);
INSTANTIATE_TEST_SUITE_P(ActionControls, SystemControlRun,
                         ::testing::ValuesIn(ActionControls()), RowName);
INSTANTIATE_TEST_SUITE_P(DISABLED_ScopedLock, SystemControlRun,
                         ::testing::Values(ScopedLock()), RowName);
INSTANTIATE_TEST_SUITE_P(StateControls, InFlightControlRun,
                         ::testing::ValuesIn(StateControls()), RowName);
INSTANTIATE_TEST_SUITE_P(DISABLED_ActionControls, InFlightControlRun,
                         ::testing::ValuesIn(ActionControls()), RowName);
INSTANTIATE_TEST_SUITE_P(DISABLED_ScopedLock, InFlightControlRun,
                         ::testing::Values(ScopedLock()), RowName);

TEST_F(AssertionRun, DISABLED_NoCallbackIsPlacedOnceTheSystemHasEnded) {
  ArmInTurn({[] {
    ASSERT_EQ(vpi_control(vpiAssertionSysEnd, nullptr), 1);
    EXPECT_EQ(WatchAssertion("top.u1.af", cbAssertionFailure), nullptr);
    EXPECT_EQ(WatchAssertionSystem(cbAssertionSysOn), nullptr);
  }});
  Run(kActionsDesign);

  EXPECT_EQ(api_.PlacedCallbackCount(), 0u);
}

TEST_F(AssertionRun, TheFailActionControlsWithholdTheDefaultReport) {
  ArmInTurn(
      {[] {
         ASSERT_NE(WatchAssertion("top.ad", cbAssertionFailure), nullptr);
         ASSERT_EQ(vpi_control(vpiAssertionSysDisableFailAction, nullptr), 1);
       },
       [] {
         ASSERT_EQ(vpi_control(vpiAssertionSysEnableFailAction, nullptr), 1);
       }});
  testing::internal::CaptureStderr();
  Run("module top;\n"
      "  logic clk = 0, v = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  ad: assert property (@(posedge clk) v);\n"
      "  initial begin #10 $arm; #10 $arm; #20 $finish; end\n"
      "endmodule\n");
  std::string err = testing::internal::GetCapturedStderr();

  int reports = 0;
  for (size_t at = err.find("ERROR top.ad ("); at != std::string::npos;
       at = err.find("ERROR top.ad (", at + 1)) {
    ++reports;
  }
  EXPECT_EQ(reports, 3);
  std::vector<uint64_t> failures;
  for (const AssertionCall& call : CallsOf(cbAssertionFailure)) {
    failures.push_back(call.cb_time);
  }
  EXPECT_EQ(failures, (std::vector<uint64_t>{15, 25, 35}));
}

TEST_F(AssertionRun, AScopeReachesTheAssertionsNestedBelowIt) {
  ArmInTurn({[] {
    ASSERT_EQ(vpi_control(vpiAssertionSysOff,
                          vpi_handle_by_name(VpiText("top.u1"), nullptr)),
              1);
  }});
  Run("interface bus(input logic clk); logic v = 0; int fails = 0;\n"
      "  ai: assert property (@(posedge clk) v) else fails++;\n"
      "endinterface\n"
      "module leaf(input logic clk); logic v = 0; int fails = 0;\n"
      "  al: assert property (@(posedge clk) v) else fails++;\n"
      "endmodule\n"
      "module m(input logic clk); logic v = 0;\n"
      "  leaf s(clk);\n"
      "  bus i(clk);\n"
      "  for (genvar k = 0; k < 1; k++) begin : g\n"
      "    int fails = 0;\n"
      "    ag: assert property (@(posedge clk) v) else fails++;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  m u1(clk);\n"
      "  m u2(clk);\n"
      "  initial begin #10 $arm; #30 $finish; end\n"
      "endmodule\n");

  for (const char* counter : {"s.fails", "i.fails", "g[0].fails"}) {
    std::string u1 = "top.u1.";
    u1 += counter;
    std::string u2 = "top.u2.";
    u2 += counter;
    EXPECT_EQ(IntOf(u1.c_str()), 1) << u1;
    EXPECT_EQ(IntOf(u2.c_str()), 4) << u2;
  }
}

}  // namespace
