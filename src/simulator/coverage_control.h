#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/code_coverage.h"

namespace delta {

enum class CoverageControl : std::uint8_t {
  kStart = 0,
  kStop = 1,
  kReset = 2,
  kCheck = 3,
};

constexpr int kCoverageTypeAssertion = 20;
constexpr int kCoverageTypeFsmState = 21;
constexpr int kCoverageTypeStatement = 22;
constexpr int kCoverageTypeToggle = 23;

constexpr std::string_view kCoverageRootScope = "$root";

enum class CoverageStatus : std::int8_t {
  kOverflow = -2,
  kError = -1,
  kNoCoverage = 0,
  kOk = 1,
  kPartial = 2,
};

enum class CoverageAvailability : std::uint8_t {
  kNone,
  kPartial,
  kFull,
};

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

class CoverageControlState {
 public:
  void SetAvailability(const std::string& scope, int coverage_type,
                       CoverageAvailability a) {
    scopes_[scope].types[coverage_type].availability = a;
  }

  bool IsRegistered(const std::string& scope) const {
    return scopes_.find(scope) != scopes_.end();
  }

  void SetModuleDefinition(const std::string& scope,
                           const std::string& definition) {
    scopes_[scope].definition = definition;
  }

  void SetCoverableItems(const std::string& scope, int coverage_type,
                         std::int64_t count) {
    scopes_[scope].coverable_items[coverage_type] = count;
  }

  void SetCoveredItems(const std::string& scope, int coverage_type,
                       std::int64_t count) {
    scopes_[scope].covered_items[coverage_type] = count;
  }

  int CoverageMax(const std::string& scope, int coverage_type,
                  bool include_below = true) const {
    return HierarchyCount(scope, coverage_type, include_below,
                          &ScopeState::coverable_items);
  }

  int CoverageGet(const std::string& scope, int coverage_type,
                  bool include_below = true) const {
    return HierarchyCount(scope, coverage_type, include_below,
                          &ScopeState::covered_items);
  }

  void RegisterCoverageDatabase(const std::string& name, bool from_this_design,
                                std::unordered_set<int> coverage_types) {
    CoverageDatabase& db = databases_[name];
    db.from_this_design = from_this_design;
    db.coverage_types = std::move(coverage_types);
  }

  void SetDatabaseCoveredItems(const std::string& name,
                               const std::string& scope, int coverage_type,
                               std::int64_t count) {
    CoverageDatabase& db = databases_[name];
    db.covered_items[scope][coverage_type] = count;
    db.coverage_types.insert(coverage_type);
  }

  CoverageStatus CoverageMerge(int coverage_type, const std::string& name) {
    auto it = databases_.find(name);
    if (it == databases_.end() && ReadDatabaseFile(name)) {
      it = databases_.find(name);
    }
    if (it == databases_.end()) {
      return CoverageStatus::kError;
    }
    CoverageDatabase& db = it->second;
    if (!db.from_this_design) {
      return CoverageStatus::kError;
    }
    if (db.coverage_types.find(coverage_type) == db.coverage_types.end()) {
      return CoverageStatus::kNoCoverage;
    }
    MergeDatabaseCoverage(db, coverage_type);
    ++db.merges;
    return CoverageStatus::kOk;
  }

  std::uint64_t MergeCount(const std::string& name) const {
    auto it = databases_.find(name);
    return it == databases_.end() ? 0 : it->second.merges;
  }

  void SetCoverageSaveShouldFail(bool fail) {
    coverage_save_should_fail_ = fail;
  }

  std::uint64_t SaveCount(const std::string& name) const {
    auto it = databases_.find(name);
    return it == databases_.end() ? 0 : it->second.saves;
  }

  CoverageStatus CoverageSave(int coverage_type, const std::string& name) {
    if (coverage_save_should_fail_) {
      RemoveDatabase(name);
      return CoverageStatus::kError;
    }
    if (!AnyScopeOffers(coverage_type)) return CoverageStatus::kNoCoverage;
    CoverageDatabase& db = databases_[name];
    db.from_this_design = true;
    db.coverage_types = {coverage_type};
    SaveCurrentCoverage(db, coverage_type);
    if (!WriteDatabaseFile(name)) {
      RemoveDatabase(name);
      return CoverageStatus::kError;
    }
    ++db.saves;
    return CoverageStatus::kOk;
  }

  void SetDatabaseDirectory(std::string directory) {
    database_directory_ = std::move(directory);
  }

  CodeCoverage& Code() { return code_; }

  bool IsCollecting(const std::string& scope, int coverage_type) const {
    const TypeState* t = FindType(scope, coverage_type);
    return t != nullptr && t->collecting;
  }

  std::uint64_t StartCount(const std::string& scope, int coverage_type) const {
    return Field(scope, coverage_type, &TypeState::started);
  }
  std::uint64_t StopCount(const std::string& scope, int coverage_type) const {
    return Field(scope, coverage_type, &TypeState::stopped);
  }
  std::uint64_t ResetCount(const std::string& scope, int coverage_type) const {
    return Field(scope, coverage_type, &TypeState::resets);
  }

  static bool ScopeIsBelow(const std::string& root,
                           const std::string& candidate) {
    return candidate.size() > root.size() + 1 &&
           candidate.compare(0, root.size(), root) == 0 &&
           candidate[root.size()] == '.';
  }

  CoverageStatus Control(CoverageControl control, int coverage_type,
                         const std::string& scope, bool include_below = true) {
    std::vector<std::string> roots = NamedScopes(scope);
    if (roots.empty()) {
      return CoverageStatus::kError;
    }
    CoverageStatus status =
        ControlHierarchy(control, coverage_type, roots.front(), include_below);
    for (std::size_t i = 1; i < roots.size(); ++i) {
      status = CombineHierarchyStatus(
          status,
          ControlHierarchy(control, coverage_type, roots[i], include_below));
    }
    return status;
  }

 private:
  struct TypeState {
    CoverageAvailability availability = CoverageAvailability::kNone;
    bool collecting = false;
    bool has_data = false;
    std::uint64_t started = 0;
    std::uint64_t stopped = 0;
    std::uint64_t resets = 0;
  };

  struct ScopeState {
    std::string definition;
    std::unordered_map<int, TypeState> types;
    std::unordered_map<int, std::int64_t> coverable_items;
    std::unordered_map<int, std::int64_t> covered_items;
  };

  std::vector<std::string> NamedScopes(const std::string& name) const {
    if (name.empty()) return {};
    if (scopes_.find(name) != scopes_.end()) return {name};
    std::vector<std::string> instances;
    for (const auto& entry : scopes_) {
      const bool kNamed = name == kCoverageRootScope
                              ? entry.first.find('.') == std::string::npos
                              : entry.second.definition == name;
      if (kNamed) instances.push_back(entry.first);
    }
    return instances;
  }

  CoverageStatus ControlHierarchy(CoverageControl control, int coverage_type,
                                  const std::string& root, bool include_below) {
    CoverageStatus status =
        ControlOne(control, coverage_type, scopes_.find(root)->second);
    if (!include_below) return status;
    for (auto& entry : scopes_) {
      if (!ScopeIsBelow(root, entry.first)) continue;
      status = CombineHierarchyStatus(
          status, ControlOne(control, coverage_type, entry.second));
    }
    return status;
  }

  CoverageStatus ControlOne(CoverageControl control, int coverage_type,
                            ScopeState& scope) {
    TypeState& s = scope.types[coverage_type];
    switch (control) {
      case CoverageControl::kStart:
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
        return CoverageStatus::kError;
      case CoverageControl::kStop:
        if (s.collecting) {
          s.collecting = false;
          ++s.stopped;
        }
        return CoverageStatus::kOk;
      case CoverageControl::kReset:
        if (s.has_data || scope.covered_items.contains(coverage_type)) {
          s.has_data = false;
          scope.covered_items.erase(coverage_type);
          ++s.resets;
        }
        return CoverageStatus::kOk;
      case CoverageControl::kCheck:
        switch (s.availability) {
          case CoverageAvailability::kNone:
            return CoverageStatus::kNoCoverage;
          case CoverageAvailability::kPartial:
            return CoverageStatus::kPartial;
          case CoverageAvailability::kFull:
            return CoverageStatus::kOk;
        }
        return CoverageStatus::kError;
    }
    return CoverageStatus::kError;
  }

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

  struct CoverageDatabase {
    bool from_this_design = false;
    std::unordered_set<int> coverage_types;
    std::unordered_map<std::string, std::unordered_map<int, std::int64_t>>
        covered_items;
    std::uint64_t merges = 0;
    std::uint64_t saves = 0;
  };

  void MergeDatabaseCoverage(const CoverageDatabase& db, int coverage_type) {
    for (const auto& entry : db.covered_items) {
      auto type_it = entry.second.find(coverage_type);
      if (type_it == entry.second.end()) continue;
      std::int64_t& covered = scopes_[entry.first].covered_items[coverage_type];
      covered = std::max(covered, type_it->second);
    }
  }

  void SaveCurrentCoverage(CoverageDatabase& db, int coverage_type) const {
    db.covered_items.clear();
    for (const auto& entry : scopes_) {
      auto type_it = entry.second.covered_items.find(coverage_type);
      if (type_it == entry.second.covered_items.end()) continue;
      db.covered_items[entry.first][coverage_type] = type_it->second;
    }
  }

  static void StartCollecting(TypeState& s) {
    if (!s.collecting) {
      s.collecting = true;
      s.has_data = true;
      ++s.started;
    }
  }

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

  static std::int64_t ScopeCount(
      const std::unordered_map<int, std::int64_t>& items, int coverage_type) {
    auto it = items.find(coverage_type);
    return it == items.end() ? 0 : it->second;
  }

  bool AnyScopeOffers(int coverage_type) const {
    return std::any_of(scopes_.begin(), scopes_.end(), [&](const auto& entry) {
      auto it = entry.second.types.find(coverage_type);
      return it != entry.second.types.end() &&
             it->second.availability != CoverageAvailability::kNone;
    });
  }

  const TypeState* FindType(const std::string& scope, int coverage_type) const {
    auto it = scopes_.find(scope);
    if (it == scopes_.end()) return nullptr;
    auto type_it = it->second.types.find(coverage_type);
    return type_it == it->second.types.end() ? nullptr : &type_it->second;
  }

  std::uint64_t Field(const std::string& scope, int coverage_type,
                      std::uint64_t TypeState::* member) const {
    const TypeState* t = FindType(scope, coverage_type);
    return t == nullptr ? 0 : t->*member;
  }

  std::unordered_map<std::string, ScopeState> scopes_;
  std::unordered_map<std::string, CoverageDatabase> databases_;
  bool coverage_save_should_fail_ = false;
  std::string database_directory_;
  CodeCoverage code_;

  std::string DatabasePath(const std::string& name) const;
  std::string DesignSignature() const;
  bool WriteDatabaseFile(const std::string& name) const;
  bool ReadDatabaseFile(const std::string& name);
  void RemoveDatabase(const std::string& name);
};

}  // namespace delta
