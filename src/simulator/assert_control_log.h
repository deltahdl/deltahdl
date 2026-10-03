#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §20.11: one call of an assertion control system task, in the terms of the
// $assertcontrol invocation it is or expands to. `scopes` holds the
// list_of_scopes_or_assertions, each item by the full hierarchical names it may
// stand for: the name as written, and the name as the caller's scope reads it.
// An empty list selects the whole design.
struct AssertControlCall {
  uint32_t control_type = 0;
  uint32_t assertion_type = 0;
  uint32_t directive_type = 0;
  uint32_t levels = 0;
  std::vector<std::vector<std::string>> scopes;
};

// §20.11: an assertion as the controls select it -- its Table 20-6 type bit,
// its Table 20-7 directive bit, the full hierarchical name of the scope it is
// written in, and its own full name, which is empty for an unlabelled one.
struct AssertionIdentity {
  uint32_t type_bit = 0;
  uint32_t directive_bit = 0;
  std::string_view scope;
  std::string_view name;
};

// §20.11: what the controls applied so far leave an assertion doing: whether
// it is checked, whether its fail action runs (the default $error included),
// whether its pass action runs on a vacuous and on a nonvacuous success, and
// whether it is locked against every control but an Unlock.
struct AssertionStatus {
  bool locked = false;
  bool checking = true;
  bool fail_action = true;
  bool vacuous_pass = true;
  bool nonvacuous_pass = true;
  // Whether the action block of a verdict that `holds`, vacuously or not,
  // runs.
  bool RunsAction(bool holds, bool vacuous) const {
    if (!holds) return fail_action;
    return vacuous ? vacuous_pass : nonvacuous_pass;
  }
};

// §20.11: whether `call` selects `assertion`, by its assertion_type and
// directive_type masks and by its scope list.
bool CallSelects(const AssertControlCall& call,
                 const AssertionIdentity& assertion);

// §20.11: the assertion control calls the run has made, in order. An
// assertion's status is the controls that select it applied in that order, so
// a Lock (control_type 1) holds it against every later call but an Unlock
// until one comes, whatever else those calls select. On, Off and Kill do not
// affect an expect statement.
class AssertControlLog {
 public:
  void Apply(AssertControlCall call);
  // Whether a call names a scope list, without which an assertion is selected
  // by its type and directive alone and its names are not needed.
  bool NamesScopes() const { return names_scopes_; }
  AssertionStatus StatusOf(const AssertionIdentity& assertion) const;

 private:
  std::vector<AssertControlCall> calls_;
  bool names_scopes_ = false;
};

}  // namespace delta
