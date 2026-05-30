#include "parser/assertion_control_task.h"

namespace delta {

AssertionControlTaskCategory ClassifyAssertionControlTask(
    std::string_view name) {
  if (name == "$asserton" || name == "$assertoff" || name == "$assertkill") {
    return AssertionControlTaskCategory::kAssertTask;
  }
  if (name == "$assertpasson" || name == "$assertpassoff" ||
      name == "$assertfailon" || name == "$assertfailoff" ||
      name == "$assertnonvacuouson" || name == "$assertvacuousoff") {
    return AssertionControlTaskCategory::kAssertActionTask;
  }
  if (name == "$assertcontrol") {
    return AssertionControlTaskCategory::kAssertControl;
  }
  return AssertionControlTaskCategory::kNotAssertionControlTask;
}

bool IsAssertionControlTaskName(std::string_view name) {
  return ClassifyAssertionControlTask(name) !=
         AssertionControlTaskCategory::kNotAssertionControlTask;
}

}  // namespace delta
