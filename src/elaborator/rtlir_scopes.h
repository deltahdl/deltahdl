#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

struct ClassDecl;
struct EventExpr;
struct Expr;
struct ModuleItem;
struct Stmt;

using GenBlockConsts = std::vector<std::pair<std::string_view, int64_t>>;

using GenBlockPrefixes = std::vector<std::string_view>;

inline bool ParamVisibleFromScopes(std::string_view decl_prefix,
                                   const GenBlockPrefixes& scopes) {
  if (decl_prefix.empty()) return true;
  for (std::string_view scope : scopes) {
    if (scope == decl_prefix) return true;
  }
  return false;
}

inline std::string_view DeclaredScopedName(
    std::string_view name, const GenBlockPrefixes& scopes,
    const std::unordered_set<std::string_view>& declared) {
  for (auto it = scopes.rbegin(); it != scopes.rend(); ++it) {
    auto found = declared.find(std::string(*it) + std::string(name));
    if (found != declared.end()) return *found;
  }
  return name;
}

struct ScopedDeclarations {
  const GenBlockPrefixes& scopes;
  const std::unordered_set<std::string_view>& declared;
};

struct HierStep {
  std::string_view name;
  bool has_index = false;
  int64_t index = 0;
  std::string_view external_name;
  std::string_view genvar;
};

using HierPath = std::vector<HierStep>;

struct RtlirGenBlockSubroutine {
  ModuleItem* decl = nullptr;
  HierPath gen_block_path;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

struct RtlirGenBlockMember {
  enum class Kind : uint8_t { kStorage, kParam, kIndex };
  Kind kind = Kind::kStorage;
  std::string_view name;
  std::string_view storage;
  size_t param_index = 0;
  int64_t index_value = 0;
  HierPath gen_block_path;
};

struct RtlirGenBlockTypedef {
  ModuleItem* item = nullptr;
  HierPath gen_block_path;
};

struct RtlirGenBlockClass {
  const ClassDecl* decl = nullptr;
  HierPath gen_block_path;
};

struct RtlirGenBlockLet {
  const ModuleItem* item = nullptr;
  HierPath gen_block_path;
  GenBlockPrefixes gen_block_prefixes;
};

struct RtlirGenBlockClocking {
  size_t index = 0;
  const ModuleItem* block = nullptr;
  HierPath gen_block_path;
  GenBlockPrefixes gen_block_prefixes;
};

struct RtlirAssertionItemDecl {
  const ModuleItem* item = nullptr;
  HierPath gen_block_path;
  GenBlockPrefixes gen_block_prefixes;
  const ModuleItem* clocking_block = nullptr;
};

struct RtlirAssertion {
  const ModuleItem* item = nullptr;
  HierPath gen_block_path;
  GenBlockPrefixes gen_block_prefixes;
  const std::vector<EventExpr>* leading_clock = nullptr;
};

inline void RecordGenBlockMember(std::vector<RtlirGenBlockMember>& members,
                                 const HierPath& path,
                                 RtlirGenBlockMember member) {
  if (path.empty()) return;
  for (const HierStep& step : path) {
    if (step.name.empty()) return;
  }
  member.gen_block_path = path;
  members.push_back(std::move(member));
}

struct InstArrayDim {
  int64_t left = 0;
  int64_t right = 0;

  [[nodiscard]] int64_t Size() const {
    return (left < right ? right - left : left - right) + 1;
  }
  [[nodiscard]] int64_t IndexFromLeft(int64_t from_left) const {
    return left <= right ? left + from_left : left - from_left;
  }
};

struct InstArrayElement {
  std::string_view name;
  int64_t left = 0;
  int64_t right = 0;
  int64_t index = 0;
  std::vector<InstArrayDim> dims;
  std::vector<int64_t> indices;
  std::vector<const Expr*> connections;
};

struct RtlirImport {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
  std::string_view scope_prefix;
};

struct RtlirBlockParamOverride {
  const Stmt* decl = nullptr;
  Expr* init = nullptr;
};

}  // namespace delta
