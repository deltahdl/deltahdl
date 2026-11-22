#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <tuple>

#include "helpers_assertion_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

struct Form {
  const char* name;
  const char* head;
};

struct QueueControl {
  const char* name;
  int operation;
  bool on_one;
  bool discards;
  bool stops;
};

constexpr Form kAssertZero = {"AssertZero", "assert #0 (x) else"};
constexpr Form kAssumeZero = {"AssumeZero", "assume #0 (x) else"};
constexpr Form kCoverZero = {"CoverZero", "cover #0 (y)"};
constexpr Form kAssertFinal = {"AssertFinal", "assert final (x) else"};
constexpr Form kAssumeFinal = {"AssumeFinal", "assume final (x) else"};
constexpr Form kCoverFinal = {"CoverFinal", "cover final (y)"};

constexpr QueueControl kReset = {"Reset", vpiAssertionReset, true, true, false};
constexpr QueueControl kKill = {"Kill", vpiAssertionKill, true, true, false};
constexpr QueueControl kDisable = {"Disable", vpiAssertionDisable, true, false,
                                   true};
constexpr QueueControl kSysReset = {"SysReset", vpiAssertionSysReset, false,
                                    true, false};
constexpr QueueControl kSysKill = {"SysKill", vpiAssertionSysKill, false, true,
                                   true};
constexpr QueueControl kSysEnd = {"SysEnd", vpiAssertionSysEnd, false, true,
                                  true};
constexpr QueueControl kSysOff = {"SysOff", vpiAssertionSysOff, false, false,
                                  true};

std::function<void()> Issue(QueueControl control, const char* target,
                            uint32_t start) {
  return [control, target, start] {
    vpiHandle handle =
        control.on_one ? vpi_handle_by_name(VpiText(target), nullptr) : nullptr;
    s_vpi_time time = {vpiSimTime, 0, start, 0.0};
    int result = control.operation == vpiAssertionKill
                     ? vpi_control(control.operation, handle, &time)
                     : vpi_control(control.operation, handle);
    EXPECT_EQ(result, 1);
  };
}

std::string DeferredDesign(const Form& form) {
  return std::string(
             "module top;\n"
             "  logic x = 0, y = 1;\n"
             "  int done1 = 0, done2 = 0;\n"
             "  function void act1(); done1++; endfunction\n"
             "  function void act2(); done2++; endfunction\n"
             "  initial begin\n"
             "    a1: ") +
         form.head + " act1();\n    a2: " + form.head +
         " act2();\n"
         "    $arm;\n"
         "  end\n"
         "endmodule\n";
}

class DeferredQueueRun
    : public AssertionRun,
      public ::testing::WithParamInterface<std::tuple<Form, QueueControl>> {};

TEST_P(DeferredQueueRun, ADiscardingControlFlushesTheQueuedReport) {
  const auto& [form, control] = GetParam();
  ArmInTurn({Issue(control, "top.a1", 0)});
  Run(DeferredDesign(form).c_str());

  EXPECT_EQ(IntOf("top.done1"), control.discards ? 0 : 1);
  EXPECT_EQ(IntOf("top.done2"), control.discards && !control.on_one ? 0 : 1);
}

constexpr const char* kProceduralTwice =
    "module top;\n"
    "  logic clk = 0, a = 0;\n"
    "  int failed1 = 0, failed2 = 0;\n"
    "  always @(posedge clk) begin\n"
    "    c1: assert property (a) else failed1++;\n"
    "    c2: assert property (a) else failed2++;\n"
    "    $arm;\n"
    "  end\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

class ProceduralQueueRun : public AssertionRun,
                           public ::testing::WithParamInterface<QueueControl> {
};

TEST_P(ProceduralQueueRun, ADiscardingControlFlushesThePendingInstance) {
  QueueControl control = GetParam();
  ArmInTurn({Issue(control, "top.c1", 5)});
  Run(kProceduralTwice);

  int first = control.discards ? 0 : 1;
  int later = control.stops ? 0 : 1;
  EXPECT_EQ(IntOf("top.failed1"), first + later);
  EXPECT_EQ(IntOf("top.failed2"),
            control.on_one ? 2 : (control.discards ? 0 : 1) + later);
}

std::string FormAndControlName(
    const ::testing::TestParamInfo<std::tuple<Form, QueueControl>>& info) {
  return std::string(std::get<0>(info.param).name) +
         std::get<1>(info.param).name;
}

std::string ControlName(const ::testing::TestParamInfo<QueueControl>& info) {
  return info.param.name;
}

::testing::internal::ParamGenerator<Form> EveryForm() {
  return ::testing::Values(kAssertZero, kAssumeZero, kCoverZero, kAssertFinal,
                           kAssumeFinal, kCoverFinal);
}

INSTANTIATE_TEST_SUITE_P(
    EveryForm, DeferredQueueRun,
    ::testing::Combine(EveryForm(),
                       ::testing::Values(kReset, kDisable, kSysReset, kSysKill,
                                         kSysEnd, kSysOff)),
    FormAndControlName);

INSTANTIATE_TEST_SUITE_P(DISABLED_EveryForm, DeferredQueueRun,
                         ::testing::Combine(EveryForm(),
                                            ::testing::Values(kKill)),
                         FormAndControlName);

INSTANTIATE_TEST_SUITE_P(EveryControl, ProceduralQueueRun,
                         ::testing::Values(kReset, kSysReset, kSysKill,
                                           kSysEnd),
                         ControlName);

INSTANTIATE_TEST_SUITE_P(DISABLED_EveryControl, ProceduralQueueRun,
                         ::testing::Values(kKill, kDisable, kSysOff),
                         ControlName);

}  // namespace
