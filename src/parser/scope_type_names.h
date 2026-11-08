#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

namespace delta {

struct ScopeTypeNames {
  std::unordered_set<std::string_view> types;
  std::unordered_set<std::string_view> nettypes;
  std::unordered_set<std::string_view> udps;
};

struct CompilationUnitScopeNames {
  ScopeTypeNames own;
  std::unordered_map<std::string_view, ScopeTypeNames> packages;
  std::unordered_map<std::string_view, ScopeTypeNames> classes;
};

inline void MergeCompilationUnitScope(CompilationUnitScopeNames& target,
                                      const CompilationUnitScopeNames& src) {
  target.own.types.insert(src.own.types.begin(), src.own.types.end());
  target.own.nettypes.insert(src.own.nettypes.begin(), src.own.nettypes.end());
  target.own.udps.insert(src.own.udps.begin(), src.own.udps.end());
  target.packages.insert(src.packages.begin(), src.packages.end());
  target.classes.insert(src.classes.begin(), src.classes.end());
}

}  // namespace delta
