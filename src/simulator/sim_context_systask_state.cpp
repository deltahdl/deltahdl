// The state a system task writes into SimContext and a later call or a test
// reads back: the $finish request of §20.2, the $timeformat and
// $timeunit/$timeprecision settings of §20.4, the severity-task report of
// §20.10, the whole-design assertion controls of §20.11, the $monitor display
// list of §21.2.3, and the optional interactive tasks of Annex D ($reset,
// $scope, $list, $showscopes, $showvars, $log). Each body only records or
// answers a value; the tasks themselves are evaluated elsewhere.
//
// It is split out of sim_context.h, where these bodies were defined inside the
// class, so the header carries the interface and no one file carries the whole
// of the context's implementation.

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

void SimContext::RequestFinish() {
  finish_requested_ = true;
  stop_requested_ = true;
}

void SimContext::RecordReset(int64_t reset_value) {
  ++reset_count_;
  reset_value_ = reset_value;
}

void SimContext::SetInteractiveScope(std::string_view name) {
  interactive_scope_ = std::string(name);
}

void SimContext::RecordListing(std::string_view name) {
  last_listed_scope_ = std::string(name);
}

void SimContext::RecordShowScopes(std::string_view scope, bool recursive) {
  last_shown_scope_ = std::string(scope);
  show_scopes_recursive_ = recursive;
}

void SimContext::RecordShowVars(std::string_view scope,
                                std::vector<std::string> vars) {
  last_showvars_scope_ = std::string(scope);
  showvars_variables_ = std::move(vars);
}

const std::vector<std::string>& SimContext::ShowVarsVariables() const {
  return showvars_variables_;
}

void SimContext::SetLogFile(std::string_view name) {
  log_file_ = std::string(name);
  logging_enabled_ = true;
}

void SimContext::SetTimeFormat(const TimeFormatSpec& spec) {
  time_format_ = spec;
  time_format_explicit_ = true;
}

void SimContext::SetCurrentScopeName(std::string_view name) {
  current_scope_name_ = std::string(name);
}

void SimContext::SetScopeTimeScale(std::string_view name, const TimeScale& ts) {
  scope_timescales_[std::string(name)] = ts;
}

const TimeScale* SimContext::FindScopeTimeScale(std::string_view name) const {
  auto it = scope_timescales_.find(std::string(name));
  return it == scope_timescales_.end() ? nullptr : &it->second;
}

void SimContext::SetGlobalAssertCheckingOff(uint32_t assertion_type,
                                            uint32_t directive_type) {
  assert_checking_off_ = true;
  assert_checking_off_atype_ = assertion_type;
  assert_checking_off_dtype_ = directive_type;
}

void SimContext::SetGlobalAssertFailActionOff(uint32_t assertion_type,
                                              uint32_t directive_type) {
  assert_fail_off_ = true;
  assert_fail_off_atype_ = assertion_type;
  assert_fail_off_dtype_ = directive_type;
}

bool SimContext::AssertFailActionEnabled(uint32_t type_bit,
                                         uint32_t directive_bit) const {
  if (!assert_fail_off_) return true;
  return (assert_fail_off_atype_ & type_bit) == 0 ||
         (assert_fail_off_dtype_ & directive_bit) == 0;
}

void SimContext::SetLastSeverity(std::string_view sev, std::string_view msg,
                                 SimTime t, std::string_view scope,
                                 uint32_t line) {
  last_severity_ = std::string(sev);
  last_severity_msg_ = std::string(msg);
  last_severity_time_ = t;
  last_severity_scope_ = std::string(scope);
  last_severity_line_ = line;
}

void SimContext::SetActiveMonitor(const Expr* call) {
  active_monitor_ = call;
  ++monitor_generation_;
}

void SimContext::SetMonitorDisplayPending(bool pending) {
  monitor_display_pending_ = pending;
}

void SimContext::SetMonitorLastValue(Variable* var, const Logic4Vec& value) {
  monitor_last_values_[var] = value;
}

}  // namespace delta
