#include "simulator/assert_control_log.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/sva_engine_queues.h"

namespace delta {

namespace {

// The parts of an assertion's status a control_type sets.
constexpr uint32_t kChecking = 1;
constexpr uint32_t kFail = 2;
constexpr uint32_t kVacuousPass = 4;
constexpr uint32_t kNonvacuousPass = 8;
constexpr uint32_t kLocking = 16;

uint32_t PartsSetBy(uint32_t control_type) {
  switch (static_cast<AssertControlType>(control_type)) {
    case AssertControlType::kOn:
    case AssertControlType::kOff:
    case AssertControlType::kKill:
      return kChecking;
    case AssertControlType::kFailOn:
    case AssertControlType::kFailOff:
      return kFail;
    case AssertControlType::kPassOn:
    case AssertControlType::kPassOff:
      return kVacuousPass | kNonvacuousPass;
    case AssertControlType::kNonvacuousOn:
      return kNonvacuousPass;
    case AssertControlType::kVacuousOff:
      return kVacuousPass;
    default:
      return kLocking;
  }
}

// Table 20-6's last three bits are violation report types, which the
// directive_type argument does not select, and so is an expect statement's:
// §20.11 checks that argument only for assertions.
bool DirectiveSelected(const AssertControlCall& call,
                       const AssertionIdentity& assertion) {
  if (assertion.type_bit >= static_cast<uint32_t>(AssertionTypeBit::kExpect)) {
    return true;
  }
  return (call.directive_type & assertion.directive_bit) != 0;
}

// Whether the scope list item `item`, by one of the names it may stand for,
// names the assertion itself or a scope that holds it within `levels` levels,
// which count as §21.7.1.2's levels of $dumpvars do: 0 is every level below
// the scope, 1 the scope alone.
bool ItemSelects(const std::vector<std::string>& item, uint32_t levels,
                 const AssertionIdentity& assertion) {
  for (const std::string& name : item) {
    if (!assertion.name.empty() && assertion.name == name) return true;
    if (assertion.scope == name) return true;
    if (assertion.scope.size() <= name.size() ||
        assertion.scope.compare(0, name.size(), name) != 0 ||
        assertion.scope[name.size()] != '.') {
      continue;
    }
    std::string_view below = assertion.scope.substr(name.size());
    auto depth =
        static_cast<uint32_t>(std::count(below.begin(), below.end(), '.'));
    if (levels == 0 || depth < levels) return true;
  }
  return false;
}

// Whether the whole-design call `later` selects every assertion `earlier`
// selects and sets every part of its status `earlier` sets, which leaves
// `earlier` nothing to decide once no call locks an assertion.
bool Supersedes(const AssertControlCall& later,
                const AssertControlCall& earlier) {
  uint32_t parts = PartsSetBy(earlier.control_type);
  return later.scopes.empty() && parts != kLocking &&
         (parts & ~PartsSetBy(later.control_type)) == 0 &&
         (earlier.assertion_type & ~later.assertion_type) == 0 &&
         (earlier.directive_type & ~later.directive_type) == 0;
}

void SetStatus(uint32_t control_type, bool is_expect, AssertionStatus& status) {
  switch (static_cast<AssertControlType>(control_type)) {
    case AssertControlType::kOn:
      status.checking = status.checking || !is_expect;
      break;
    case AssertControlType::kOff:
    case AssertControlType::kKill:
      status.checking = status.checking && is_expect;
      break;
    case AssertControlType::kPassOn:
      status.vacuous_pass = true;
      status.nonvacuous_pass = true;
      break;
    case AssertControlType::kPassOff:
      status.vacuous_pass = false;
      status.nonvacuous_pass = false;
      break;
    case AssertControlType::kFailOn:
      status.fail_action = true;
      break;
    case AssertControlType::kFailOff:
      status.fail_action = false;
      break;
    case AssertControlType::kNonvacuousOn:
      status.nonvacuous_pass = true;
      break;
    case AssertControlType::kVacuousOff:
      status.vacuous_pass = false;
      break;
    default:
      break;
  }
}

}  // namespace

bool CallSelects(const AssertControlCall& call,
                 const AssertionIdentity& assertion) {
  if ((call.assertion_type & assertion.type_bit) == 0) return false;
  if (!DirectiveSelected(call, assertion)) return false;
  if (call.scopes.empty()) return true;
  return std::any_of(call.scopes.begin(), call.scopes.end(),
                     [&](const std::vector<std::string>& item) {
                       return ItemSelects(item, call.levels, assertion);
                     });
}

void AssertControlLog::Apply(AssertControlCall call) {
  bool locks_any = std::any_of(
      calls_.begin(), calls_.end(), [](const AssertControlCall& earlier) {
        return PartsSetBy(earlier.control_type) == kLocking;
      });
  if (!locks_any) {
    std::erase_if(calls_, [&](const AssertControlCall& earlier) {
      return Supersedes(call, earlier);
    });
  }
  names_scopes_ = names_scopes_ || !call.scopes.empty();
  calls_.push_back(std::move(call));
}

AssertionStatus AssertControlLog::StatusOf(
    const AssertionIdentity& assertion) const {
  AssertionStatus status;
  bool is_expect =
      assertion.type_bit == static_cast<uint32_t>(AssertionTypeBit::kExpect);
  for (const AssertControlCall& call : calls_) {
    if (!CallSelects(call, assertion)) continue;
    auto control = static_cast<AssertControlType>(call.control_type);
    if (control == AssertControlType::kUnlock) {
      status.locked = false;
    } else if (!status.locked) {
      status.locked = control == AssertControlType::kLock;
      SetStatus(call.control_type, is_expect, status);
    }
  }
  return status;
}

}  // namespace delta
