#include <algorithm>
#include <string_view>
#include <utility>

#include "common/string_methods.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"

// The built-in tasks and functions the procedure walk names a call of: the
// methods of §9.7's process class and of §15's semaphore and mailbox, and the
// system functions the standard defines. They are lists the standard fixes,
// kept apart from the walk that consults them.

namespace delta {

// §9.7, §15.3 and §15.4: the kind of tf call a call of the method `method` of
// the built-in class `cls` is, zero for none. Every method the three classes
// declare is listed but new, which no statement calls through a variable.
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
  return std::ranges::any_of(kFunctions, kIsCalled) ? vpiMethodFuncCall : 0;
}

// Whether `name` is a built-in system function, every one the standard defines
// listed by the clause defining it: §14.14, §16.14.7, §18.13, §19.9, and the
// functions of §20.3 to §20.15, §21.3 and §21.6. $cast (§8.16), $system
// (§20.17.1) and $stacktrace (§20.17.2) may each be called as a task or a
// function, and a statement calling one calls the task.
bool VpiIsBuiltInSystemFunction(std::string_view name) {
  static constexpr std::string_view kFunctions[] = {
      // §14.14, §16.14.7, §18.13 and §19.9.
      "$global_clock", "$inferred_clock", "$inferred_disable", "$urandom",
      "$urandom_range", "$get_coverage",
      // §20.3 and §20.4.
      "$realtime", "$stime", "$time", "$timeunit", "$timeprecision",
      // §20.5 and §20.6.
      "$bitstoreal", "$realtobits", "$bitstoshortreal", "$shortrealtobits",
      "$itor", "$rtoi", "$signed", "$unsigned", "$bits", "$isunbounded",
      "$typename",
      // §20.7.
      "$unpacked_dimensions", "$dimensions", "$left", "$right", "$low", "$high",
      "$increment", "$size",
      // §20.8.
      "$clog2", "$ln", "$log10", "$exp", "$sqrt", "$pow", "$floor", "$ceil",
      "$sin", "$cos", "$tan", "$asin", "$acos", "$atan", "$atan2", "$hypot",
      "$sinh", "$cosh", "$tanh", "$asinh", "$acosh", "$atanh",
      // §20.9.
      "$countbits", "$countones", "$onehot", "$onehot0", "$isunknown",
      // §20.12.
      "$sampled", "$rose", "$fell", "$stable", "$changed", "$past",
      "$past_gclk", "$rose_gclk", "$fell_gclk", "$stable_gclk", "$changed_gclk",
      "$future_gclk", "$rising_gclk", "$falling_gclk", "$steady_gclk",
      "$changing_gclk",
      // §20.13, §20.14 and §20.15.
      "$coverage_control", "$coverage_get_max", "$coverage_get",
      "$coverage_merge", "$coverage_save", "$random", "$dist_chi_square",
      "$dist_erlang", "$dist_exponential", "$dist_normal", "$dist_poisson",
      "$dist_t", "$dist_uniform", "$q_full",
      // §21.3 and §21.6.
      "$fopen", "$fgetc", "$ungetc", "$fgets", "$fscanf", "$sscanf", "$fread",
      "$ftell", "$fseek", "$rewind", "$feof", "$ferror", "$sformatf",
      "$test$plusargs", "$value$plusargs"};
  return std::ranges::any_of(kFunctions, [name](std::string_view function) {
    return function == name;
  });
}

// Whether `method` is one of the built-in methods of a value of `holder`'s
// kind, every one listed by name: §6.16's of a string, §6.19.5's of an enum,
// §7.5's of a dynamic array, §7.9's of an associative array, §7.10.2's of a
// queue, and §7.12's of any unpacked array but the ordering methods of
// §7.12.2, which an associative array has none of. Each is a function.
bool VpiIsBuiltInMethod(VpiBuiltInHolder holder, std::string_view method) {
  static constexpr std::string_view kEnum[] = {"first", "last", "next",
                                               "prev",  "num",  "name"};
  static constexpr std::string_view kDynamic[] = {"size", "delete"};
  static constexpr std::string_view kAssoc[] = {
      "num", "size", "delete", "exists", "first", "last", "next", "prev"};
  static constexpr std::string_view kQueue[] = {
      "size",     "insert",     "delete",   "pop_front",
      "pop_back", "push_front", "push_back"};
  static constexpr std::string_view kManipulation[] = {
      "find",       "find_index",
      "find_first", "find_first_index",
      "find_last",  "find_last_index",
      "min",        "max",
      "unique",     "unique_index",
      "sum",        "product",
      "and",        "or",
      "xor",        "map"};
  static constexpr std::string_view kOrdering[] = {"reverse", "sort", "rsort",
                                                   "shuffle"};
  const auto kLists = [method](const auto& names) {
    return std::ranges::any_of(
        names, [method](std::string_view name) { return name == method; });
  };
  switch (holder) {
    case VpiBuiltInHolder::kString:
      return StringMethodWritesItsObject(method) ||
             StringMethodAnswersAValue(method);
    case VpiBuiltInHolder::kEnum:
      return kLists(kEnum);
    case VpiBuiltInHolder::kNone:
      return false;
    default:
      break;
  }
  if (kLists(kManipulation)) return true;
  if (holder == VpiBuiltInHolder::kAssocArray) return kLists(kAssoc);
  if (kLists(kOrdering)) return true;
  if (holder == VpiBuiltInHolder::kDynamicArray) return kLists(kDynamic);
  return holder == VpiBuiltInHolder::kQueue && kLists(kQueue);
}

}  // namespace delta
