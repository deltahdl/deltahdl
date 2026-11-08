#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

struct AssertControlCall {
  uint32_t control_type = 0;
  uint32_t assertion_type = 0;
  uint32_t directive_type = 0;
  uint32_t levels = 0;
  std::vector<std::vector<std::string>> scopes;
};

struct AssertionIdentity {
  uint32_t type_bit = 0;
  uint32_t directive_bit = 0;
  std::string_view scope;
  std::string_view name;
};

struct AssertionStatus {
  bool locked = false;
  bool checking = true;
  bool fail_action = true;
  bool vacuous_pass = true;
  bool nonvacuous_pass = true;
  bool RunsAction(bool holds, bool vacuous) const {
    if (!holds) return fail_action;
    return vacuous ? vacuous_pass : nonvacuous_pass;
  }
};

bool CallSelects(const AssertControlCall& call,
                 const AssertionIdentity& assertion);

class AssertControlLog {
 public:
  void Apply(AssertControlCall call);
  bool NamesScopes() const { return names_scopes_; }
  AssertionStatus StatusOf(const AssertionIdentity& assertion) const;

 private:
  std::vector<AssertControlCall> calls_;
  bool names_scopes_ = false;
};

}  // namespace delta
