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
#include <unordered_set>

namespace delta {

// §40.3.1 control-constant values accepted in the first argument.
enum class CoverageControl : std::uint8_t {
  kStart = 0,
  kStop = 1,
  kReset = 2,
  kCheck = 3,
};

// §40.3.1 status values returned by $coverage_control. The numeric values match
// the `SV_COV_* `define macros.
enum class CoverageStatus : std::int8_t {
  kOverflow = -2,
  kError = -1,
  kNoCoverage = 0,
  kOk = 1,
  kPartial = 2,
};

// How much coverage a scope offers for the requested coverage type. A real
// coverage engine derives this from the coverable items the design holds; the
// model stores it so the control rules can be exercised without that engine.
enum class CoverageAvailability : std::uint8_t {
  kNone,     // scope exists but offers no coverage of the requested type
  kPartial,  // some, but not all, of the scope is coverable
  kFull,     // the whole scope is coverable
};

// Decodes the first $coverage_control argument into a control action. Returns
// false for a value that is not one of the four §40.3.1 control constants.
inline bool CoverageControlFromInt(int value, CoverageControl *out) {
  switch (value) {
    case 0:
      *out = CoverageControl::kStart;
      return true;
    case 1:
      *out = CoverageControl::kStop;
      return true;
    case 2:
      *out = CoverageControl::kReset;
      return true;
    case 3:
      *out = CoverageControl::kCheck;
      return true;
    default:
      return false;
  }
}

// Tracks the coverage-collection state of the named hierarchy scopes and
// applies the §40.3.2.1 control rules to them.
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

  // Registers the number of coverable items of `coverage_type` a scope has
  // actually covered so far, mirroring what a real coverage engine accumulates
  // as collection proceeds. §40.3.2.3 reports this count, summed over the
  // hierarchy, as the current coverage level. Unlike the coverable-item count,
  // this varies with the collection state over the simulation.
  void SetCoveredItems(const std::string &scope, int coverage_type,
                       std::int64_t count) {
    scopes_[scope].covered_items[coverage_type] = count;
  }

  // §40.3.2.2 ($coverage_get_max): returns the value representing 100% coverage
  // for `coverage_type` over `scope` — the sum of all coverable items of that
  // type in the hierarchy. That sum is a property of the design structure, not
  // of the collection state, so it stays constant for the whole simulation;
  // starting, stopping, or resetting coverage never changes it.
  //
  // The integer result follows §40.3.2.2: a scope the design does not contain
  // is a bad argument (`SV_COV_ERROR); a scope with no coverable items of the
  // type offers no coverage (`SV_COV_NOCOV, 0); a count too large to represent
  // as an integer overflows (`SV_COV_OVERFLOW); otherwise the positive sum is
  // the maximum coverage number.
  int CoverageMax(const std::string &scope, int coverage_type) const {
    auto it = scopes_.find(scope);
    if (it == scopes_.end()) {
      return static_cast<int>(CoverageStatus::kError);
    }
    auto type_it = it->second.coverable_items.find(coverage_type);
    if (type_it == it->second.coverable_items.end() || type_it->second <= 0) {
      return static_cast<int>(CoverageStatus::kNoCoverage);
    }
    if (type_it->second >
        static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max())) {
      return static_cast<int>(CoverageStatus::kOverflow);
    }
    return static_cast<int>(type_it->second);
  }

  // §40.3.2.3 ($coverage_get): returns the current coverage value for
  // `coverage_type` over `scope` — the sum of the coverable items of that type
  // that have been covered so far in the hierarchy. The return follows the same
  // pattern as §40.3.2.2, but the positive value is the current coverage level
  // rather than the maximum, so it can grow as collection proceeds.
  //
  // The integer result follows §40.3.2.3: a scope the design does not contain
  // is a bad argument (`SV_COV_ERROR); a count too large to represent as an
  // integer overflows (`SV_COV_OVERFLOW); a coverage type with nothing covered
  // (no entry, or none of its items covered yet) reports no coverage
  // (`SV_COV_NOCOV, 0, since a positive value is strictly greater than zero);
  // otherwise the positive count is the current coverage number.
  int CoverageGet(const std::string &scope, int coverage_type) const {
    auto it = scopes_.find(scope);
    if (it == scopes_.end()) {
      return static_cast<int>(CoverageStatus::kError);
    }
    auto type_it = it->second.covered_items.find(coverage_type);
    if (type_it == it->second.covered_items.end() || type_it->second <= 0) {
      return static_cast<int>(CoverageStatus::kNoCoverage);
    }
    if (type_it->second >
        static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max())) {
      return static_cast<int>(CoverageStatus::kOverflow);
    }
    return static_cast<int>(type_it->second);
  }

  // Registers a named coverage database the tool could load, mirroring what a
  // real coverage engine would find when asked to merge by name. §40.3.2.4 keys
  // the database by an arbitrary, implementation-specific `name`; this model
  // stores it by that string. `from_this_design` records whether the database
  // corresponds to the design being simulated, and `coverage_types` lists the
  // §40.3.1 coverage-type constants the database holds — the two properties
  // §40.3.2.4 inspects to decide the outcome of a merge.
  void RegisterCoverageDatabase(const std::string &name, bool from_this_design,
                                std::unordered_set<int> coverage_types) {
    CoverageDatabase &db = databases_[name];
    db.from_this_design = from_this_design;
    db.coverage_types = std::move(coverage_types);
  }

  // §40.3.2.4 ($coverage_merge): loads and merges coverage data of
  // `coverage_type` from the database located by `name` into the simulation,
  // and returns the resulting §40.3.1 status.
  //
  //   `SV_COV_OK    — the database was found, belongs to this design, and holds
  //                   the requested coverage type, so its data are merged.
  //   `SV_COV_NOCOV — the database was found but does not contain the requested
  //                   coverage type, so there is nothing of that type to merge.
  //   `SV_COV_ERROR — the database was not found, or does not correspond to
  //   this
  //                   design, or another error occurred. §40.3.2.4 requires an
  //                   error when `name` does not exist or is from a different
  //                   design.
  CoverageStatus CoverageMerge(int coverage_type, const std::string &name) {
    auto it = databases_.find(name);
    // The name does not exist: no database to load. §40.3.2.4 requires an
    // error.
    if (it == databases_.end()) {
      return CoverageStatus::kError;
    }
    CoverageDatabase &db = it->second;
    // The database is from a different design: §40.3.2.4 requires an error.
    if (!db.from_this_design) {
      return CoverageStatus::kError;
    }
    // The database exists for this design but does not hold the requested type:
    // the data were found but did not contain the coverage type requested.
    if (db.coverage_types.find(coverage_type) == db.coverage_types.end()) {
      return CoverageStatus::kNoCoverage;
    }
    // The data are found and merged.
    ++db.merges;
    return CoverageStatus::kOk;
  }

  // Number of successful merges performed against a named database. A merge
  // only happens on the `SV_COV_OK path, so this makes the "merged" effect of
  // $coverage_merge observable rather than just the returned status.
  std::uint64_t MergeCount(const std::string &name) const {
    auto it = databases_.find(name);
    return it == databases_.end() ? 0 : it->second.merges;
  }

  // §40.3.2.5: records which §40.3.1 coverage types are currently available to
  // be saved from this design, mirroring what a real coverage engine has
  // collected. $coverage_save reports `SV_COV_NOCOV (and saves nothing) for a
  // type that is not available here.
  void SetCoverageAvailableForSave(int coverage_type, bool available) {
    if (available) {
      savable_coverage_types_.insert(coverage_type);
    } else {
      savable_coverage_types_.erase(coverage_type);
    }
  }

  // §40.3.2.5: forces the next save to report an error, mirroring a tool-side
  // failure while writing the coverage database. This exercises the error path,
  // including the required removal of the entry being written.
  void SetCoverageSaveShouldFail(bool fail) {
    coverage_save_should_fail_ = fail;
  }

  // Number of successful saves recorded under a named database. A save only
  // records data on the `SV_COV_OK path, so this makes the "saved" effect of
  // $coverage_save observable rather than just the returned status.
  std::uint64_t SaveCount(const std::string &name) const {
    auto it = databases_.find(name);
    return it == databases_.end() ? 0 : it->second.saves;
  }

  // §40.3.2.5 ($coverage_save): saves the current coverage of `coverage_type`
  // to the tool's coverage database under `name` and returns the resulting
  // §40.3.1 status. Saving never touches the simulation's coverage-collection
  // state, so this method only writes the database side.
  //
  //   `SV_COV_OK    — the coverage data are saved. The entry records that it
  //                   belongs to this design and holds the saved type, so a
  //                   later $coverage_merge() with the same name can load it
  //                   (§40.3.2.4). Overwriting an entry left by a previous save
  //                   is not an error.
  //   `SV_COV_NOCOV — no coverage of the requested type is available in this
  //                   design, so there is nothing to save and no entry is
  //                   written.
  //   `SV_COV_ERROR — an error occurred during the save. The entry for `name`
  //   is
  //                   removed so a partial write cannot corrupt the database.
  CoverageStatus CoverageSave(int coverage_type, const std::string &name) {
    // An error during the save: remove the entry being written for `name` to
    // preserve database integrity. This also discards any entry a previous
    // successful save left under the same name.
    if (coverage_save_should_fail_) {
      databases_.erase(name);
      return CoverageStatus::kError;
    }
    // No coverage of the requested type is available in this design: nothing is
    // saved and no entry is written.
    if (savable_coverage_types_.find(coverage_type) ==
        savable_coverage_types_.end()) {
      return CoverageStatus::kNoCoverage;
    }
    // Write (or overwrite) the entry to reflect the current state: it belongs
    // to this design and holds the saved coverage type.
    CoverageDatabase &db = databases_[name];
    db.from_this_design = true;
    db.coverage_types = {coverage_type};
    ++db.saves;
    return CoverageStatus::kOk;
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

  // Performs the §40.3.2.1 action selected by `control` over `scope` and
  // returns the resulting §40.3.1 status.
  CoverageStatus Control(CoverageControl control, const std::string &scope) {
    auto it = scopes_.find(scope);
    // A scope the design does not contain is a bad argument: §40.3.2.1 reports
    // `SV_COV_ERROR for errors such as a nonexisting module.
    if (it == scopes_.end()) {
      return CoverageStatus::kError;
    }
    ScopeState &s = it->second;
    switch (control) {
      case CoverageControl::kStart:
        // `SV_COV_START starts collection where coverage is available. Starting
        // a scope that is already collecting has no effect, but still reports
        // success.
        switch (s.availability) {
          case CoverageAvailability::kNone:
            return CoverageStatus::kNoCoverage;
          case CoverageAvailability::kPartial:
            StartCollecting(s);
            return CoverageStatus::kPartial;
          case CoverageAvailability::kFull:
            StartCollecting(s);
            return CoverageStatus::kOk;
        }
        return CoverageStatus::kError;  // unreachable
      case CoverageControl::kStop:
        // `SV_COV_STOP stops collection; stopping a scope that is not
        // collecting has no effect. The operation reports success regardless.
        if (s.collecting) {
          s.collecting = false;
          ++s.stopped;
        }
        return CoverageStatus::kOk;
      case CoverageControl::kReset:
        // `SV_COV_RESET clears collected coverage; it has no effect when no
        // coverage has been collected, so repeated resets do nothing after the
        // first. The operation reports success regardless.
        if (s.has_data) {
          s.has_data = false;
          ++s.resets;
        }
        return CoverageStatus::kOk;
      case CoverageControl::kCheck:
        // `SV_COV_CHECK reports whether coverage can be obtained without
        // changing the collection state.
        switch (s.availability) {
          case CoverageAvailability::kNone:
            return CoverageStatus::kNoCoverage;
          case CoverageAvailability::kPartial:
            return CoverageStatus::kPartial;
          case CoverageAvailability::kFull:
            return CoverageStatus::kOk;
        }
        return CoverageStatus::kError;  // unreachable
    }
    return CoverageStatus::kError;
  }

 private:
  struct ScopeState {
    CoverageAvailability availability = CoverageAvailability::kNone;
    bool collecting = false;
    bool has_data = false;  // coverage accumulated since the last reset
    std::uint64_t started = 0;
    std::uint64_t stopped = 0;
    std::uint64_t resets = 0;
    // §40.3.2.2: coverable-item counts per coverage type, used to compute the
    // 100% (maximum) coverage value. Keyed by the §40.3.1 coverage-type
    // constant (`SV_COV_ASSERTION, `SV_COV_FSM_STATE, ...).
    std::unordered_map<int, std::int64_t> coverable_items;
    // §40.3.2.3: covered-item counts per coverage type, used to report the
    // current coverage level. Keyed by the §40.3.1 coverage-type constant.
    std::unordered_map<int, std::int64_t> covered_items;
  };

  // §40.3.2.4: a named coverage database that $coverage_merge can load.
  struct CoverageDatabase {
    // Whether the saved database corresponds to the design being simulated.
    bool from_this_design = false;
    // The §40.3.1 coverage-type constants the database holds.
    std::unordered_set<int> coverage_types;
    // Successful merges performed against this database.
    std::uint64_t merges = 0;
    // §40.3.2.5: successful saves recorded under this database.
    std::uint64_t saves = 0;
  };

  // Begins collection on a scope that is not already collecting. A scope
  // already collecting is left untouched so that a repeated start has no
  // effect.
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
  // §40.3.2.4: named coverage databases available to $coverage_merge, and
  // §40.3.2.5: written by $coverage_save.
  std::unordered_map<std::string, CoverageDatabase> databases_;
  // §40.3.2.5: coverage types currently available to save from this design.
  std::unordered_set<int> savable_coverage_types_;
  // §40.3.2.5: when set, the next save reports an error.
  bool coverage_save_should_fail_ = false;
};

}  // namespace delta
