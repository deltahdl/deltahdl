#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

// §20.11 (Syntax 20-12): the assertion control system tasks fall into three
// categories. assert_task is $asserton, $assertoff, or $assertkill;
// assert_action_task is $assertpasson, $assertpassoff, $assertfailon,
// $assertfailoff, $assertnonvacuouson, or $assertvacuousoff; and the general
// $assertcontrol task takes a control_type and optional type/level/list
// arguments.
enum class AssertionControlTaskCategory : uint8_t {
  kAssertTask,
  kAssertActionTask,
  kAssertControl,
  kNotAssertionControlTask,
};

// §20.11 (Syntax 20-12): classify a system task name (including the leading
// '$') against the assertion control task grammar.
AssertionControlTaskCategory ClassifyAssertionControlTask(
    std::string_view name);

// §20.11: convenience predicate — whether the name is any assertion control
// system task (assert_task, assert_action_task, or $assertcontrol).
bool IsAssertionControlTaskName(std::string_view name);

}  // namespace delta
