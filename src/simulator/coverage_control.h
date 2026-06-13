#pragma once

// IEEE 1800-2023 §40.3.2.1 "$coverage_control".
//
// $coverage_control(control_constant, coverage_type, scope_def,
//                   modules_or_instance) starts, stops, resets, or queries
// coverage collection over a portion of the design hierarchy and returns one of
// the §40.3.1 status values. The control constants (`SV_COV_START,
// `SV_COV_STOP, `SV_COV_RESET, `SV_COV_CHECK) and the status values
// (`SV_COV_OK, `SV_COV_ERROR, `SV_COV_NOCOV, `SV_COV_PARTIAL) are the `define
// macros of §40.3.1; this model interprets their numeric values at run time.
//
// The control rules are encoded here as a small per-scope state model so they
// can be exercised directly; the simulator's $coverage_control entry point
// drives the same model when it evaluates a call. This mirrors the §40.5.2
// coverage-query helpers in vpi_coverage.h.

#include <cstdint>
#include <limits>
#include <string>
#include <unordered_map>

namespace delta {

// §40.3.1 control-constant values accepted in the first argument.
enum class CoverageControl : int {
  Start = 0,
  Stop = 1,
  Reset = 2,
  Check = 3,
};

// §40.3.1 status values returned by $coverage_control. The numeric values match
// the `SV_COV_* `define macros.
enum class CoverageStatus : int {
  Overflow = -2,
  Error = -1,
  NoCoverage = 0,
  Ok = 1,
  Partial = 2,
};

// How much coverage a scope offers for the requested coverage type. A real
// coverage engine derives this from the coverable items the design holds; the
// model stores it so the control rules can be exercised without that engine.
enum class CoverageAvailability {
  None,     // scope exists but offers no coverage of the requested type
  Partial,  // some, but not all, of the scope is coverable
  Full,     // the whole scope is coverable
};

// Decodes the first $coverage_control argument into a control action. Returns
// false for a value that is not one of the four §40.3.1 control constants.
inline bool CoverageControlFromInt(int value, CoverageControl *out) {
  switch (value) {
    case 0:
      *out = CoverageControl::Start;
      return true;
    case 1:
      *out = CoverageControl::Stop;
      return true;
    case 2:
      *out = CoverageControl::Reset;
      return true;
    case 3:
      *out = CoverageControl::Check;
      return true;
    default:
      return false;
  }
}

// Tracks the coverage-collection state of the named hierarchy scopes and applies
// the §40.3.2.1 control rules to them.
class CoverageControlState {
 public:
  // Registers (or updates) the coverage a named scope offers, mirroring what a
  // real coverage engine determines for the design. A scope that has never been
  // registered is treated as a nonexisting module.
  void SetAvailability(const std::string &scope, CoverageAvailability a) {
    scopes_[scope].availability = a;
  }

  bool IsRegistered(const std::string &scope) const {
    return scopes_.find(scope) != scopes_.end();
  }

  // Registers the number of coverable items of `coverage_type` a scope holds,
  // mirroring what a real coverage engine derives from the design structure.
  // §40.3.2.2 reports this count, summed over the hierarchy, as the value that
  // represents 100% coverage of that type.
  void SetCoverableItems(const std::string &scope, int coverage_type,
                         std::int64_t count) {
    scopes_[scope].coverable_items[coverage_type] = count;
  }

  // §40.3.2.2 ($coverage_get_max): returns the value representing 100% coverage
  // for `coverage_type` over `scope` — the sum of all coverable items of that
  // type in the hierarchy. That sum is a property of the design structure, not
  // of the collection state, so it stays constant for the whole simulation;
  // starting, stopping, or resetting coverage never changes it.
  //
  // The integer result follows §40.3.2.2: a scope the design does not contain is
  // a bad argument (`SV_COV_ERROR); a scope with no coverable items of the type
  // offers no coverage (`SV_COV_NOCOV, 0); a count too large to represent as an
  // integer overflows (`SV_COV_OVERFLOW); otherwise the positive sum is the
  // maximum coverage number.
  int CoverageMax(const std::string &scope, int coverage_type) const {
    auto it = scopes_.find(scope);
    if (it == scopes_.end()) {
      return static_cast<int>(CoverageStatus::Error);
    }
    auto type_it = it->second.coverable_items.find(coverage_type);
    if (type_it == it->second.coverable_items.end() || type_it->second <= 0) {
      return static_cast<int>(CoverageStatus::NoCoverage);
    }
    if (type_it->second >
        static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max())) {
      return static_cast<int>(CoverageStatus::Overflow);
    }
    return static_cast<int>(type_it->second);
  }

  bool IsCollecting(const std::string &scope) const {
    auto it = scopes_.find(scope);
    return it != scopes_.end() && it->second.collecting;
  }

  // Genuine state transitions a scope has undergone. These make the "no effect"
  // rule observable: a redundant start, stop, or reset must not advance them.
  std::uint64_t StartCount(const std::string &scope) const {
    return Field(scope, &ScopeState::started);
  }
  std::uint64_t StopCount(const std::string &scope) const {
    return Field(scope, &ScopeState::stopped);
  }
  std::uint64_t ResetCount(const std::string &scope) const {
    return Field(scope, &ScopeState::resets);
  }

  // Performs the §40.3.2.1 action selected by `control` over `scope` and returns
  // the resulting §40.3.1 status.
  CoverageStatus Control(CoverageControl control, const std::string &scope) {
    auto it = scopes_.find(scope);
    // A scope the design does not contain is a bad argument: §40.3.2.1 reports
    // `SV_COV_ERROR for errors such as a nonexisting module.
    if (it == scopes_.end()) {
      return CoverageStatus::Error;
    }
    ScopeState &s = it->second;
    switch (control) {
      case CoverageControl::Start:
        // `SV_COV_START starts collection where coverage is available. Starting
        // a scope that is already collecting has no effect, but still reports
        // success.
        switch (s.availability) {
          case CoverageAvailability::None:
            return CoverageStatus::NoCoverage;
          case CoverageAvailability::Partial:
            StartCollecting(s);
            return CoverageStatus::Partial;
          case CoverageAvailability::Full:
            StartCollecting(s);
            return CoverageStatus::Ok;
        }
        return CoverageStatus::Error;  // unreachable
      case CoverageControl::Stop:
        // `SV_COV_STOP stops collection; stopping a scope that is not collecting
        // has no effect. The operation reports success regardless.
        if (s.collecting) {
          s.collecting = false;
          ++s.stopped;
        }
        return CoverageStatus::Ok;
      case CoverageControl::Reset:
        // `SV_COV_RESET clears collected coverage; it has no effect when no
        // coverage has been collected, so repeated resets do nothing after the
        // first. The operation reports success regardless.
        if (s.has_data) {
          s.has_data = false;
          ++s.resets;
        }
        return CoverageStatus::Ok;
      case CoverageControl::Check:
        // `SV_COV_CHECK reports whether coverage can be obtained without
        // changing the collection state.
        switch (s.availability) {
          case CoverageAvailability::None:
            return CoverageStatus::NoCoverage;
          case CoverageAvailability::Partial:
            return CoverageStatus::Partial;
          case CoverageAvailability::Full:
            return CoverageStatus::Ok;
        }
        return CoverageStatus::Error;  // unreachable
    }
    return CoverageStatus::Error;
  }

 private:
  struct ScopeState {
    CoverageAvailability availability = CoverageAvailability::None;
    bool collecting = false;
    bool has_data = false;  // coverage accumulated since the last reset
    std::uint64_t started = 0;
    std::uint64_t stopped = 0;
    std::uint64_t resets = 0;
    // §40.3.2.2: coverable-item counts per coverage type, used to compute the
    // 100% (maximum) coverage value. Keyed by the §40.3.1 coverage-type
    // constant (`SV_COV_ASSERTION, `SV_COV_FSM_STATE, ...).
    std::unordered_map<int, std::int64_t> coverable_items;
  };

  // Begins collection on a scope that is not already collecting. A scope already
  // collecting is left untouched so that a repeated start has no effect.
  static void StartCollecting(ScopeState &s) {
    if (!s.collecting) {
      s.collecting = true;
      s.has_data = true;
      ++s.started;
    }
  }

  std::uint64_t Field(const std::string &scope,
                      std::uint64_t ScopeState::*member) const {
    auto it = scopes_.find(scope);
    return it == scopes_.end() ? 0 : it->second.*member;
  }

  std::unordered_map<std::string, ScopeState> scopes_;
};

}  // namespace delta
