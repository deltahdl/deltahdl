#pragma once

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

inline constexpr const char* kActionsDesign =
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

inline constexpr const char* kU1 = "top.u1";
inline constexpr const char* kU2 = "top.u2";

struct Counts {
  int pn = 0;
  int pv = 0;
  int fl = 0;
  int mf = 0;
  int mn = 0;
  int mv = 0;
};

inline constexpr Counts kUncontrolled = {80, 80, 80, 75, 60, 60};
inline constexpr Counts kOffFromTheFirstArm = {5, 5, 5, 15, 25, 25};
inline constexpr Counts kOffUntilTheSecondArm = {65, 65, 65, 50, 25, 25};
inline constexpr Counts kKilledUntilTheSecondArm = {65, 65, 65, 35, 0, 0};
inline constexpr Counts kEndedAtTheFirstArm = {5, 5, 5, 0, 0, 0};
inline constexpr Counts kOffFromTheSecondArm = {20, 20, 20, 40, 60, 60};
inline constexpr Counts kVacuousOffFromTheFirstArm = {80, 5, 80, 75, 60, 25};
inline constexpr Counts kActionsOffUntilTheSecondArm = {65, 65, 65, 50, 25, 25};

struct Op {
  int arm = 0;
  int operation = 0;
  std::string target{};
  int result = 1;
};

struct ControlRun {
  const char* name;
  std::vector<Op> ops;
  Counts u1;
  Counts u2;
  std::vector<uint64_t> u1_failures;
};

inline ControlRun Everywhere(const char* name, std::vector<Op> ops,
                             Counts counts, std::vector<uint64_t> u1_failures) {
  return {name, std::move(ops), counts, counts, std::move(u1_failures)};
}

inline void Apply(const Op& op) {
  vpiHandle handle =
      op.target.empty()
          ? nullptr
          : vpi_handle_by_name(VpiText(op.target.c_str()), nullptr);
  EXPECT_EQ(vpi_control(op.operation, handle), op.result)
      << "operation " << op.operation << " at arm " << op.arm;
}

inline Counts CountsOf(const std::string& instance) {
  Counts counts;
  for (auto [field, name] :
       {std::pair{&Counts::pn, "pn"}, std::pair{&Counts::pv, "pv"},
        std::pair{&Counts::fl, "fl"}, std::pair{&Counts::mf, "mf"},
        std::pair{&Counts::mn, "mn"}, std::pair{&Counts::mv, "mv"}}) {
    counts.*field = IntOf((instance + "." + name).c_str());
  }
  return counts;
}

inline std::array<int, 3> Settled(const Counts& c) {
  return {c.pn, c.pv, c.fl};
}

inline std::array<int, 3> InFlight(const Counts& c) {
  return {c.mf, c.mn, c.mv};
}

inline std::vector<uint64_t> EveryFailure() { return {15, 25, 35}; }

class ControlTableRun : public AssertionRun,
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

  void ExpectSettled() {
    EXPECT_EQ(Settled(CountsOf(kU1)), Settled(GetParam().u1));
    EXPECT_EQ(Settled(CountsOf(kU2)), Settled(GetParam().u2));
    std::vector<uint64_t> failures;
    for (const AssertionCall& call : CallsOf(cbAssertionFailure)) {
      failures.push_back(call.cb_time);
    }
    EXPECT_EQ(failures, GetParam().u1_failures);
  }

  void ExpectInFlight() {
    EXPECT_EQ(InFlight(CountsOf(kU1)), InFlight(GetParam().u1));
    EXPECT_EQ(InFlight(CountsOf(kU2)), InFlight(GetParam().u2));
  }
};

inline std::string RowName(const ::testing::TestParamInfo<ControlRun>& info) {
  return info.param.name;
}

}  // namespace delta
