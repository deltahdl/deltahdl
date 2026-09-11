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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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
inline bool CoverageControlFromInt(int value, CoverageControl* out) {
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
  void SetAvailability(const std::string& scope, CoverageAvailability a) {
    scopes_[scope].availability = a;
  }

  bool IsRegistered(const std::string& scope) const {
    return scopes_.find(scope) != scopes_.end();
  }

  // Registers the module definition a scope is an instance of, mirroring what
  // elaboration records against each instance it creates. §40.3.2.1 Table 40-2
  // gives the string beside the scope_def two readings, and this is what tells
  // them apart: an instance name is the hierarchical path of one scope, while a
  // definition name stands for "all instances of the given module" and so names
  // as many scopes as the design instantiated. That second reading is why
  // §40.3.2.2 and §40.3.2.3 sum over "hierarchy(ies)" rather than over one
  // hierarchy. A scope registered without a definition is an instance of
  // nothing any string can name, and is reachable only by its own path.
  void SetModuleDefinition(const std::string& scope,
                           const std::string& definition) {
    scopes_[scope].definition = definition;
  }

  // Registers the number of coverable items of `coverage_type` a scope holds,
  // mirroring what a real coverage engine derives from the design structure.
  // §40.3.2.2 reports this count, summed over the hierarchy, as the value that
  // represents 100% coverage of that type.
  void SetCoverableItems(const std::string& scope, int coverage_type,
                         std::int64_t count) {
    scopes_[scope].coverable_items[coverage_type] = count;
  }

  // Registers the number of coverable items of `coverage_type` a scope has
  // actually covered so far, mirroring what a real coverage engine accumulates
  // as collection proceeds. §40.3.2.3 reports this count, summed over the
  // hierarchy, as the current coverage level. Unlike the coverable-item count,
  // this varies with the collection state over the simulation.
  void SetCoveredItems(const std::string& scope, int coverage_type,
                       std::int64_t count) {
    scopes_[scope].covered_items[coverage_type] = count;
  }

  // §40.3.2.2 ($coverage_get_max): returns the value representing 100% coverage
  // for `coverage_type` over `scope` — the sum of all coverable items of that
  // type "over the given hierarchy(ies)". `scope` is read per §40.3.2.1, so it
  // is one instance or, as a module definition name, every instance of that
  // module, which is the plural the clause writes. That sum is a property of
  // the design structure, not of the collection state, so it stays constant for
  // the whole simulation; starting, stopping, or resetting coverage never
  // changes it.
  //
  // The integer result follows §40.3.2.2: a string the design holds no scope
  // for is a bad argument (`SV_COV_ERROR); scopes with no coverable items of
  // the type offer no coverage (`SV_COV_NOCOV, 0); a count too large to
  // represent as an integer overflows (`SV_COV_OVERFLOW); otherwise the
  // positive sum is the maximum coverage number.
  int CoverageMax(const std::string& scope, int coverage_type,
                  bool include_below = true) const {
    return HierarchyCount(scope, coverage_type, include_below,
                          &ScopeState::coverable_items);
  }

  // §40.3.2.3 ($coverage_get): returns the current coverage value for
  // `coverage_type` over `scope` — the sum of the coverable items of that type
  // that have been covered so far in the hierarchy, or in every hierarchy where
  // `scope` is a module definition name. The return follows the same pattern as
  // §40.3.2.2, but the positive value is the current coverage level rather than
  // the maximum, so it can grow as collection proceeds.
  //
  // The integer result follows §40.3.2.3: a string the design holds no scope
  // for is a bad argument (`SV_COV_ERROR); a count too large to represent as an
  // integer overflows (`SV_COV_OVERFLOW); a coverage type with nothing covered
  // (no entry, or none of its items covered yet) reports no coverage
  // (`SV_COV_NOCOV, 0, since a positive value is strictly greater than zero);
  // otherwise the positive count is the current coverage number.
  int CoverageGet(const std::string& scope, int coverage_type,
                  bool include_below = true) const {
    return HierarchyCount(scope, coverage_type, include_below,
                          &ScopeState::covered_items);
  }

  // Registers a named coverage database the tool could load, mirroring what a
  // real coverage engine would find when asked to merge by name. §40.3.2.4 keys
  // the database by an arbitrary, implementation-specific `name`; this model
  // stores it by that string. `from_this_design` records whether the database
  // corresponds to the design being simulated, and `coverage_types` lists the
  // §40.3.1 coverage-type constants the database holds — the two properties
  // §40.3.2.4 inspects to decide the outcome of a merge.
  void RegisterCoverageDatabase(const std::string& name, bool from_this_design,
                                std::unordered_set<int> coverage_types) {
    CoverageDatabase& db = databases_[name];
    db.from_this_design = from_this_design;
    db.coverage_types = std::move(coverage_types);
  }

  // Records a piece of the coverage data a named database holds: the number of
  // items of `coverage_type` that stood covered in `scope` when the database
  // was written. §40.3.2.4 loads coverage data into the simulator, so this is
  // what a merge of that type has to bring in, and it mirrors what a real
  // coverage engine would read out of the file it located by that name. A
  // database holding covered items of a type is a database that contains that
  // type, so recording data adds the type to what the database holds.
  void SetDatabaseCoveredItems(const std::string& name,
                               const std::string& scope, int coverage_type,
                               std::int64_t count) {
    CoverageDatabase& db = databases_[name];
    db.covered_items[scope][coverage_type] = count;
    db.coverage_types.insert(coverage_type);
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
  CoverageStatus CoverageMerge(int coverage_type, const std::string& name) {
    auto it = databases_.find(name);
    // The name does not exist: no database to load. §40.3.2.4 requires an
    // error.
    if (it == databases_.end()) {
      return CoverageStatus::kError;
    }
    CoverageDatabase& db = it->second;
    // The database is from a different design: §40.3.2.4 requires an error.
    if (!db.from_this_design) {
      return CoverageStatus::kError;
    }
    // The database exists for this design but does not hold the requested type:
    // the data were found but did not contain the coverage type requested.
    if (db.coverage_types.find(coverage_type) == db.coverage_types.end()) {
      return CoverageStatus::kNoCoverage;
    }
    // The data are found and merged. §40.3.2.4 loads them "into the
    // simulator", so what the database holds of the requested type joins the
    // coverage this simulation has collected and is reported from then on by
    // §40.3.2.3 - which is the sense in which coverage numbers this simulation
    // generates depend on the load having gone through.
    MergeDatabaseCoverage(db, coverage_type);
    ++db.merges;
    return CoverageStatus::kOk;
  }

  // Number of successful merges performed against a named database. A merge
  // only happens on the `SV_COV_OK path, so this makes the "merged" effect of
  // $coverage_merge observable rather than just the returned status.
  std::uint64_t MergeCount(const std::string& name) const {
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
  std::uint64_t SaveCount(const std::string& name) const {
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
  CoverageStatus CoverageSave(int coverage_type, const std::string& name) {
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
    // to this design, holds the saved coverage type, and carries the coverage
    // that stood at the moment of the save, which §40.3.2.5 requires back from
    // a later $coverage_merge() of the same name.
    CoverageDatabase& db = databases_[name];
    db.from_this_design = true;
    db.coverage_types = {coverage_type};
    SaveCurrentCoverage(db, coverage_type);
    ++db.saves;
    return CoverageStatus::kOk;
  }

  bool IsCollecting(const std::string& scope) const {
    auto it = scopes_.find(scope);
    return it != scopes_.end() && it->second.collecting;
  }

  // Genuine state transitions a scope has undergone. These make the "no effect"
  // rule observable: a redundant start, stop, or reset must not advance them.
  std::uint64_t StartCount(const std::string& scope) const {
    return Field(scope, &ScopeState::started);
  }
  std::uint64_t StopCount(const std::string& scope) const {
    return Field(scope, &ScopeState::stopped);
  }
  std::uint64_t ResetCount(const std::string& scope) const {
    return Field(scope, &ScopeState::resets);
  }

  // §40.3.2.1 Table 40-2: how far below a root one call reaches depends on the
  // scope_def argument beside the scope. `SV_COV_HIER names "the named instance
  // and any hierarchy below it"; `SV_COV_MODULE names "just the named instance,
  // excluding any hierarchy in instances below that instance". A scope lies
  // below another when its hierarchical path continues that path past a dot.
  static bool ScopeIsBelow(const std::string& root,
                           const std::string& candidate) {
    return candidate.size() > root.size() + 1 &&
           candidate.compare(0, root.size(), root) == 0 &&
           candidate[root.size()] == '.';
  }

  // Performs the §40.3.2.1 action selected by `control` over every scope
  // `scope` names - one instance, or every instance of a module definition -
  // and returns the resulting §40.3.1 status of the whole of it.
  CoverageStatus Control(CoverageControl control, const std::string& scope,
                         bool include_below = true) {
    std::vector<std::string> roots = NamedScopes(scope);
    // A string that names no scope is a bad argument: §40.3.2.1 reports
    // `SV_COV_ERROR for errors such as a nonexisting module.
    if (roots.empty()) {
      return CoverageStatus::kError;
    }
    CoverageStatus status =
        ControlHierarchy(control, roots.front(), include_below);
    // Table 40-2's definition-name column applies the operation to all
    // instances of the module, so the status reported is of all of them
    // together, on the same reading of a partly covered hierarchy.
    for (std::size_t i = 1; i < roots.size(); ++i) {
      status = CombineHierarchyStatus(
          status, ControlHierarchy(control, roots[i], include_below));
    }
    return status;
  }

 private:
  struct ScopeState {
    // §40.3.2.1 Table 40-2: the module definition this scope is an instance of,
    // which is the name the table's definition-name column reaches it by. Empty
    // where nothing registered one.
    std::string definition;
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

  // §40.3.2.1 Table 40-2's two columns: the root scopes one string names. A
  // string that is the hierarchical path of a registered scope is that
  // instance, and only that instance; any other string is read as a module
  // definition name, which names every instance of that module. The path is
  // tried first because the table's note has instance names "referenced by
  // hierarchical paths", so a string the design registered a scope under is the
  // scope it registered - reading it as a definition instead would reach that
  // scope only when some other instance happened to share the name. A string
  // that is neither names nothing, which is the nonexisting module §40.3.2.1
  // calls a bad argument; the empty string of a call that named no scope at all
  // is one of those, rather than a definition every undeclared instance shares.
  std::vector<std::string> NamedScopes(const std::string& name) const {
    if (name.empty()) return {};
    if (scopes_.find(name) != scopes_.end()) return {name};
    std::vector<std::string> instances;
    for (const auto& entry : scopes_) {
      if (entry.second.definition == name) instances.push_back(entry.first);
    }
    return instances;
  }

  // The action over one root scope and, where the scope_def argument said to
  // include it, the hierarchy below that root.
  CoverageStatus ControlHierarchy(CoverageControl control,
                                  const std::string& root, bool include_below) {
    CoverageStatus status = ControlOne(control, scopes_.find(root)->second);
    if (!include_below) return status;
    // §40.3.2.1: over a hierarchy, the operation is applied to everything in it
    // and the status reported is of the hierarchy - `SV_COV_PARTIAL "denotes
    // that coverage is only partially available in the specified hierarchy",
    // which is what a scope below the named one reporting something else makes
    // of a start or a check.
    for (auto& entry : scopes_) {
      if (!ScopeIsBelow(root, entry.first)) continue;
      status =
          CombineHierarchyStatus(status, ControlOne(control, entry.second));
    }
    return status;
  }

  // The one-scope control, which the hierarchy walk above applies to each scope
  // it names.
  CoverageStatus ControlOne(CoverageControl control, ScopeState& s) {
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
        // `SV_COV_RESET "resets all available coverage information in the
        // specified hierarchy", and the covered-item counts are that
        // information: they are what §40.3.2.3 reads back as the current
        // coverage value, so a reset leaves that value reporting that nothing
        // has been covered rather than the count it stood at. The
        // coverable-item counts §40.3.2.2 reports are not coverage information
        // but a property of the design structure, and a reset leaves them
        // alone, since that value "shall remain constant across the duration of
        // the simulation" - which is what keeps coverage% a fraction of the
        // same whole after a reset as before one. The reset has no effect when
        // there is nothing collected to clear, so repeated resets do nothing
        // after the first.
        if (s.has_data || !s.covered_items.empty()) {
          s.has_data = false;
          s.covered_items.clear();
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

  // §40.3.2.1: the status of a hierarchy, given the status of what has been
  // walked so far and of one more scope in it. Full coverage everywhere is
  // `SV_COV_OK and none anywhere is `SV_COV_NOCOV; anything in between - some
  // of the hierarchy covered and some not - is the `SV_COV_PARTIAL the clause
  // gives a start or a check over a partially available hierarchy. An error
  // stands, since a bad argument is not made good by the rest of the walk.
  static CoverageStatus CombineHierarchyStatus(CoverageStatus so_far,
                                               CoverageStatus next) {
    if (so_far == CoverageStatus::kError || next == CoverageStatus::kError) {
      return CoverageStatus::kError;
    }
    if (so_far == next) return so_far;
    if (so_far == CoverageStatus::kOk || next == CoverageStatus::kOk ||
        so_far == CoverageStatus::kPartial ||
        next == CoverageStatus::kPartial) {
      return CoverageStatus::kPartial;
    }
    return so_far;
  }

  // §40.3.2.4: a named coverage database that $coverage_merge can load.
  struct CoverageDatabase {
    // Whether the saved database corresponds to the design being simulated.
    bool from_this_design = false;
    // The §40.3.1 coverage-type constants the database holds.
    std::unordered_set<int> coverage_types;
    // §40.3.2.4: the coverage data the database holds - the covered-item counts
    // each scope stood at when the database was written, keyed by hierarchical
    // path and then by the §40.3.1 coverage-type constant. These are what a
    // merge loads into the simulation.
    std::unordered_map<std::string, std::unordered_map<int, std::int64_t>>
        covered_items;
    // Successful merges performed against this database.
    std::uint64_t merges = 0;
    // §40.3.2.5: successful saves recorded under this database.
    std::uint64_t saves = 0;
  };

  // §40.3.2.4: loads the coverage data of one type from a database into the
  // scopes of this simulation. Coverage data are the items that have been
  // covered, so merging two sets of them is their union: the merged count is at
  // least the larger of the two counts and at most their sum, and a count alone
  // cannot say which items the two sides hold in common. The larger is what
  // this takes, because summing could carry a scope past the coverable items
  // §40.3.2.2 fixes for the design, and no design covers more items than it
  // has. Only the requested type is loaded, that being the coverage the call
  // names, and a scope the database says nothing about keeps what it had.
  void MergeDatabaseCoverage(const CoverageDatabase& db, int coverage_type) {
    for (const auto& entry : db.covered_items) {
      auto type_it = entry.second.find(coverage_type);
      if (type_it == entry.second.end()) continue;
      std::int64_t& covered = scopes_[entry.first].covered_items[coverage_type];
      covered = std::max(covered, type_it->second);
    }
  }

  // §40.3.2.5: writes "the current state of coverage" of one type into a
  // database entry - the covered-item count every scope stands at, which is
  // what §40.3.2.4 loads back when the same name is merged. The entry holds the
  // state as it was when the save ran rather than a view that follows
  // collection afterwards, so what was there from an earlier save under the
  // same name goes; a save names one coverage type, so the rest of what the
  // scopes have covered is no part of it.
  void SaveCurrentCoverage(CoverageDatabase& db, int coverage_type) const {
    db.covered_items.clear();
    for (const auto& entry : scopes_) {
      auto type_it = entry.second.covered_items.find(coverage_type);
      if (type_it == entry.second.covered_items.end()) continue;
      db.covered_items[entry.first][coverage_type] = type_it->second;
    }
  }

  // Begins collection on a scope that is not already collecting. A scope
  // already collecting is left untouched so that a repeated start has no
  // effect.
  static void StartCollecting(ScopeState& s) {
    if (!s.collecting) {
      s.collecting = true;
      s.has_data = true;
      ++s.started;
    }
  }

  // §40.3.2.1 Table 40-2 for the two query functions: the count of one
  // coverage type over the scopes a call names - the scopes the string names,
  // and the hierarchy below each of them where the scope_def argument said to
  // include it. Summing over the instances of a module definition is what
  // §40.3.2.2 and §40.3.2.3 mean by the count "over the given hierarchy(ies)".
  // The §40.3.2.2/§40.3.2.3 result rules are applied to the sum: a string the
  // design holds no scope for is a bad argument, a sum of nothing is no
  // coverage, and a sum too large to represent overflows.
  int HierarchyCount(
      const std::string& scope, int coverage_type, bool include_below,
      std::unordered_map<int, std::int64_t> ScopeState::* member) const {
    std::vector<std::string> roots = NamedScopes(scope);
    if (roots.empty()) {
      return static_cast<int>(CoverageStatus::kError);
    }
    std::int64_t total = 0;
    for (const auto& root : roots) {
      total += HierarchyItems(root, coverage_type, include_below, member);
    }
    if (total <= 0) {
      return static_cast<int>(CoverageStatus::kNoCoverage);
    }
    if (total >
        static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max())) {
      return static_cast<int>(CoverageStatus::kOverflow);
    }
    return static_cast<int>(total);
  }

  // The count of one coverage type over one root scope and, where the scope_def
  // argument said to include it, the hierarchy below that root.
  std::int64_t HierarchyItems(
      const std::string& root, int coverage_type, bool include_below,
      std::unordered_map<int, std::int64_t> ScopeState::* member) const {
    std::int64_t total =
        ScopeCount(scopes_.find(root)->second.*member, coverage_type);
    if (!include_below) return total;
    for (const auto& entry : scopes_) {
      if (!ScopeIsBelow(root, entry.first)) continue;
      total += ScopeCount(entry.second.*member, coverage_type);
    }
    return total;
  }

  // One scope's count of a coverage type, which is nothing where it holds no
  // items of that type.
  static std::int64_t ScopeCount(
      const std::unordered_map<int, std::int64_t>& items, int coverage_type) {
    auto it = items.find(coverage_type);
    return it == items.end() ? 0 : it->second;
  }

  std::uint64_t Field(const std::string& scope,
                      std::uint64_t ScopeState::* member) const {
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
