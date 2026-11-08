#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <map>
#include <string>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kTwoInstances =
    "module m(input logic clk, input logic a);\n"
    "  a1: assert property (@(posedge clk) a);\n"
    "  assert property (@(posedge clk) a);\n"
    "endmodule\n"
    "module top;\n"
    "  logic clk = 0, a = 1;\n"
    "  m u1(clk, a);\n"
    "  m u2(clk, a);\n"
    "  initial $arm;\n"
    "endmodule\n";

TEST_F(AssertionRun, SameNamedAssertionsOfTwoInstancesAreApart) {
  AssertionArmer() = [] {
    ASSERT_NE(WatchAssertion("top.u1.a1", cbAssertionDisable), nullptr);
    vpiHandle other = vpi_handle_by_name(VpiText("top.u2.a1"), nullptr);
    EXPECT_EQ(vpi_control(vpiAssertionDisable, other), 1);
    EXPECT_TRUE(AssertionCalls().empty());
    vpiHandle own = vpi_handle_by_name(VpiText("top.u1.a1"), nullptr);
    EXPECT_EQ(vpi_control(vpiAssertionEnable, other), 1);
    EXPECT_EQ(vpi_control(vpiAssertionDisable, own), 1);
  };
  Run(kTwoInstances);

  ASSERT_EQ(CallsOf(cbAssertionDisable).size(), 1u);
  EXPECT_EQ(CallsOf(cbAssertionDisable)[0].assertion, "top.u1.a1");
  EXPECT_FALSE(api_.AssertionEnabled("top.u1.a1"));
  EXPECT_TRUE(api_.AssertionEnabled("top.u2.a1"));
}

TEST_F(AssertionRun, AnUnnamedAssertionTakesCallbacksAndControls) {
  AssertionArmer() = [] {
    vpiHandle own = UnnamedAssertOf("top.u1");
    vpiHandle other = UnnamedAssertOf("top.u2");
    ASSERT_NE(own, nullptr);
    ASSERT_NE(other, nullptr);
    ASSERT_NE(vpi_register_assertion_cb(own, cbAssertionDisable,
                                        &RecordAssertionCall, nullptr),
              nullptr);
    EXPECT_EQ(vpi_control(vpiAssertionDisable, other), 1);
    EXPECT_TRUE(AssertionCalls().empty());
    EXPECT_EQ(vpi_control(vpiAssertionDisable, own), 1);
  };
  Run(kTwoInstances);

  EXPECT_EQ(CallsOf(cbAssertionDisable).size(), 1u);
}

struct Timing {
  uint64_t cb_time = 0;
  uint64_t attempt_start = 0;
  bool operator==(const Timing&) const = default;
};
std::vector<Timing> TimingsOf(const std::vector<AssertionCall>& calls) {
  std::vector<Timing> timings;
  for (const AssertionCall& call : calls) {
    EXPECT_TRUE(call.has_info);
    EXPECT_EQ(call.now, call.cb_time);
    timings.push_back({call.cb_time, call.attempt_start});
  }
  return timings;
}

void WatchFor(const char* full_name, std::initializer_list<int> reasons) {
  for (int reason : reasons) {
    ASSERT_NE(WatchAssertion(full_name, reason), nullptr);
  }
}

TEST_F(AssertionRun, AConcurrentAssertionsAttemptsReachTheirCallbacks) {
  AssertionArmer() = [] {
    WatchFor("top.a1", {cbAssertionStart, cbAssertionSuccess,
                        cbAssertionVacuousSuccess, cbAssertionFailure});
  };
  Run("module top;\n"
      "  logic clk = 0, a = 0, b = 0;\n"
      "  a1: assert property (@(posedge clk) a |-> ##1 b) else begin end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    a = 1;\n"
      "    #10 clk = 1;\n"
      "    #5 clk = 0; a = 0; b = 1;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0; a = 1; b = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0; a = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionStart)),
            (std::vector<Timing>{{10, 10}, {20, 20}, {30, 30}, {40, 40}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionSuccess)),
            (std::vector<Timing>{{20, 10}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionVacuousSuccess)),
            (std::vector<Timing>{{20, 20}, {40, 40}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionFailure)),
            (std::vector<Timing>{{40, 30}}));
}

TEST_F(AssertionRun, ASequencePropertysAttemptsReachTheirCallbacks) {
  AssertionArmer() = [] {
    WatchFor("top.s1",
             {cbAssertionStart, cbAssertionSuccess, cbAssertionFailure});
  };
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 0;\n"
      "  s1: assert property (@(posedge clk) strong(a ##1 b)) else begin end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #10 clk = 1;\n"
      "    #5 clk = 0; a = 0; b = 1;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0; a = 1; b = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();

  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionStart)),
            (std::vector<Timing>{{10, 10}, {20, 20}, {30, 30}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionSuccess)),
            (std::vector<Timing>{{20, 10}}));
  ASSERT_EQ(CallsOf(cbAssertionFailure).size(), 2u);
  EXPECT_EQ(CallsOf(cbAssertionFailure)[0].cb_time, 20u);
  EXPECT_EQ(CallsOf(cbAssertionFailure)[0].attempt_start, 20u);
  EXPECT_EQ(CallsOf(cbAssertionFailure)[1].attempt_start, 30u);
}

TEST_F(AssertionRun, AnImmediateAssertionsAttemptsReachTheirCallbacks) {
  AssertionArmer() = [] {
    vpiHandle i1 = vpi_handle_by_name(VpiText("top.i1"), nullptr);
    ASSERT_NE(i1, nullptr);
    EXPECT_EQ(vpi_get(vpiType, i1), vpiImmediateAssert);
    EXPECT_STREQ(vpi_get_str(vpiFullName, i1), "top.i1");
    for (int reason :
         {cbAssertionStart, cbAssertionSuccess, cbAssertionFailure}) {
      ASSERT_NE(
          vpi_register_assertion_cb(i1, reason, &RecordAssertionCall, nullptr),
          nullptr);
    }
  };
  Run("module top;\n"
      "  logic clk = 0, x = 1;\n"
      "  always @(posedge clk) begin\n"
      "    i1: assert (x) else begin end\n"
      "  end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #2 clk = 1;\n"
      "    #2 clk = 0; x = 0;\n"
      "    #2 clk = 1;\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionStart)),
            (std::vector<Timing>{{2, 2}, {6, 6}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionSuccess)),
            (std::vector<Timing>{{2, 2}}));
  EXPECT_EQ(TimingsOf(CallsOf(cbAssertionFailure)),
            (std::vector<Timing>{{6, 6}}));
}

TEST_F(AssertionRun, ADisabledAttemptReachesTheDisabledEvaluationCallback) {
  AssertionArmer() = [] {
    WatchFor("top.a1", {cbAssertionDisabledEvaluation, cbAssertionSuccess,
                        cbAssertionFailure});
    WatchFor("top.a2", {cbAssertionDisabledEvaluation});
    WatchFor("top.a3", {cbAssertionDisabledEvaluation});
  };
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 0, rst = 0;\n"
      "  a1: assert property (@(posedge clk) disable iff (rst) a |-> ##2 b)\n"
      "      else begin end\n"
      "  a2: assert property (@(posedge clk) disable iff (rst) a) else begin "
      "end\n"
      "  a3: assert property (@(posedge clk) disable iff (rst) a ##2 b)\n"
      "      else begin end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #10 clk = 1;\n"
      "    #5 clk = 0; rst = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n");

  std::map<std::string, std::vector<AssertionCall>> by_assertion;
  for (const AssertionCall& call : CallsOf(cbAssertionDisabledEvaluation)) {
    by_assertion[call.assertion].push_back(call);
  }
  EXPECT_EQ(TimingsOf(by_assertion["top.a1"]),
            (std::vector<Timing>{{20, 10}, {20, 20}}));
  EXPECT_EQ(TimingsOf(by_assertion["top.a2"]), (std::vector<Timing>{{20, 20}}));
  EXPECT_EQ(TimingsOf(by_assertion["top.a3"]),
            (std::vector<Timing>{{20, 10}, {20, 20}}));
  EXPECT_TRUE(CallsOf(cbAssertionSuccess).empty());
  EXPECT_TRUE(CallsOf(cbAssertionFailure).empty());
}

std::string Written(vpiHandle expr) {
  const char* text =
      expr != nullptr ? vpi_get_str(vpiDecompile, expr) : nullptr;
  return text != nullptr ? text : "";
}

struct Detail {
  std::vector<std::string> exprs;
  int from = -1;
  int to = -1;
  bool operator==(const Detail&) const = default;
};

std::vector<Detail>& Details() {
  static std::vector<Detail> details;
  return details;
}

PLI_INT32 RecordDetail(PLI_INT32 reason, p_vpi_time, vpiHandle,
                       p_vpi_attempt_info info, PLI_BYTE8*) {
  Detail detail;
  if (reason == cbAssertionFailure) {
    detail.exprs.push_back(Written(info->detail.failExpr));
  } else {
    const s_vpi_assertion_step_info& step = *info->detail.step;
    for (PLI_INT32 i = 0; i < step.matched_expression_count; ++i) {
      detail.exprs.push_back(Written(step.matched_exprs[i]));
    }
    detail.from = step.stateFrom;
    detail.to = step.stateTo;
  }
  Details().push_back(detail);
  return 0;
}

void WatchDetail(const char* full_name, std::initializer_list<int> reasons) {
  vpiHandle assertion = vpi_handle_by_name(VpiText(full_name), nullptr);
  for (int reason : reasons) {
    ASSERT_NE(
        vpi_register_assertion_cb(assertion, reason, &RecordDetail, nullptr),
        nullptr);
  }
}

TEST_F(AssertionRun, AttemptDetailNamesTheAssertionsExpressions) {
  Details().clear();
  AssertionArmer() = [this] {
    WatchDetail("top.a1", {cbAssertionFailure, cbAssertionStepFailure});
    AssertionAttemptInfo failed;
    failed.attempt_start_time = 1;
    failed.fail_expr = "b";
    api_.DeliverAssertionEvent("top.a1", cbAssertionFailure, 2, failed);
    AssertionAttemptInfo stepped;
    stepped.attempt_start_time = 1;
    stepped.step = {{"a", "b"}, 0, 2};
    api_.DeliverAssertionEvent("top.a1", cbAssertionStepFailure, 2, stepped);
  };
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 0;\n"
      "  a1: assert property (@(posedge clk) a |-> b) else begin end\n"
      "  initial $arm;\n"
      "endmodule\n");

  EXPECT_EQ(Details(),
            (std::vector<Detail>{{{"b"}, -1, -1}, {{"a", "b"}, 0, 2}}));
}

std::vector<std::string> SortedTexts() {
  std::vector<std::string> texts;
  for (const Detail& detail : Details()) {
    texts.insert(texts.end(), detail.exprs.begin(), detail.exprs.end());
  }
  std::sort(texts.begin(), texts.end());
  return texts;
}

TEST_F(AssertionRun, ARunsFailureNamesTheExpressionTheAttemptFailedAt) {
  Details().clear();
  AssertionArmer() = [] {
    WatchDetail("top.a1", {cbAssertionFailure});
    WatchDetail("top.a2", {cbAssertionFailure});
    WatchDetail("top.a3", {cbAssertionFailure});
  };
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 0, c = 0;\n"
      "  a1: assert property (@(posedge clk) a |-> b) else begin end\n"
      "  a2: assert property (@(posedge clk) a ##1 c) else begin end\n"
      "  a3: assert property (@(posedge clk) b) else begin end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(SortedTexts(), (std::vector<std::string>{"b", "b", "b", "b", "c"}));
}

void EnableStepAt(const char* full_name, uint32_t start) {
  s_vpi_time time = {vpiSimTime, 0, start, 0.0};
  EXPECT_EQ(vpi_control(vpiAssertionEnableStep,
                        vpi_handle_by_name(VpiText(full_name), nullptr), &time,
                        vpiAssertionClockSteps),
            1);
}

constexpr const char* kFourEdges =
    "  initial begin\n"
    "    $arm;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

TEST_F(AssertionRun, AStepEnabledAttemptCallsItsStepCallbackEachTick) {
  Details().clear();
  AssertionArmer() = [] {
    WatchDetail("top.a1", {cbAssertionStepSuccess});
    EnableStepAt("top.a1", 15);
  };
  Run(std::string("module top;\n"
                  "  logic clk = 0, a = 1, b = 1, c = 1;\n"
                  "  a1: assert property (@(posedge clk) a ##1 b ##1 c)\n"
                  "      else begin end\n") +
      kFourEdges);

  EXPECT_EQ(Details(),
            (std::vector<Detail>{{{"a"}, 0, 2}, {{"b"}, 2, 3}, {{"c"}, 3, 1}}));
}

TEST_F(AssertionRun, AStepEnabledAttemptsFailingStepEndsWithItsFailure) {
  Details().clear();
  AssertionArmer() = [] {
    WatchDetail("top.a1", {cbAssertionStepSuccess});
    EnableStepAt("top.a1", 5);
  };
  Run(std::string("module top;\n"
                  "  logic clk = 0, a = 1, d = 0;\n"
                  "  a1: assert property (@(posedge clk) a ##1 d)\n"
                  "      else begin end\n") +
      kFourEdges);

  EXPECT_EQ(Details(), (std::vector<Detail>{{{"a"}, 0, 2}, {{"d"}, 2, 2}}));
}

}  // namespace
}  // namespace delta
