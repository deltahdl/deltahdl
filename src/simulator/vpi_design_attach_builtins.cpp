#include <algorithm>
#include <string_view>
#include <utility>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"

// The built-in tasks and functions the procedure walk names a call of: the
// methods of §9.7's process class, of §15's semaphore and mailbox and of every
// class (§18). They are lists the standard fixes, kept apart from the walk that
// consults them.

namespace delta {

// §9.7, §15.3 and §15.4: the kind of tf call a call of the method `method` of
// the built-in class `cls` is, zero for none. Every method the three classes
// declare is listed but new, which no statement calls through a variable; the
// built-in methods every class has (§18) are each class's too.
int VpiBuiltInClassCallKind(std::string_view cls, std::string_view method) {
  using Method = std::pair<std::string_view, std::string_view>;
  static constexpr Method kTasks[] = {
      {"process", "await"}, {"semaphore", "get"}, {"mailbox", "put"},
      {"mailbox", "get"},   {"mailbox", "peek"},
  };
  static constexpr Method kFunctions[] = {
      {"process", "self"},          {"process", "status"},
      {"process", "kill"},          {"process", "suspend"},
      {"process", "resume"},        {"process", "srandom"},
      {"process", "get_randstate"}, {"process", "set_randstate"},
      {"semaphore", "put"},         {"semaphore", "try_get"},
      {"mailbox", "num"},           {"mailbox", "try_put"},
      {"mailbox", "try_get"},       {"mailbox", "try_peek"},
  };
  const auto kIsCalled = [&](const Method& entry) {
    return entry.first == cls && entry.second == method;
  };
  if (std::ranges::any_of(kTasks, kIsCalled)) return vpiMethodTaskCall;
  if (std::ranges::any_of(kFunctions, kIsCalled)) return vpiMethodFuncCall;
  static constexpr std::string_view kClasses[] = {"process", "semaphore",
                                                  "mailbox"};
  const bool kBuiltInClass = std::ranges::any_of(
      kClasses, [cls](std::string_view name) { return name == cls; });
  return kBuiltInClass && VpiIsClassBuiltInMethod(method) ? vpiMethodFuncCall
                                                          : 0;
}

int VpiMemberBuiltInCallKind(std::string_view method) {
  return method == "rand_mode" || method == "constraint_mode"
             ? vpiMethodFuncCall
             : 0;
}

bool VpiIsClassBuiltInMethod(std::string_view method) {
  static constexpr std::string_view kMethods[] = {
      "randomize",       "pre_randomize", "post_randomize", "rand_mode",
      "constraint_mode", "srandom",       "get_randstate",  "set_randstate"};
  return std::ranges::any_of(
      kMethods, [method](std::string_view name) { return name == method; });
}

}  // namespace delta
