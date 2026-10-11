#include <algorithm>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_key_match.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §10.9.2 (printed page 264): every member is covered by a member key, a type
// key whose type matches the member's, or `default:`.
void CheckPatternCoverage(const std::vector<StructMember>& members,
                          const std::unordered_set<std::string_view>& seen,
                          const std::vector<std::string_view>& type_keys,
                          const StructPatternTarget& target) {
  for (const auto& m : members) {
    if (seen.count(m.name) != 0) continue;
    bool typed = std::ranges::any_of(type_keys, [&](std::string_view key) {
      return TypeKeyMatchesMember(key, m, target.typedefs);
    });
    if (typed) continue;
    target.diag.Error(
        target.loc,
        std::format("member '{}' not covered by assignment pattern", m.name),
        Subclause("10.9.2"));
    return;
  }
}

// §10.9 gives `structure_pattern_key ::= member_identifier |
// assignment_pattern_key`, so every key of a structure pattern is a name -- a
// member's, `default`, or a type's -- and the key's text is that name.
void CheckPatternKeys(const Expr* pattern,
                      const std::vector<StructMember>& members,
                      const StructPatternTarget& target) {
  std::unordered_set<std::string_view> member_names;
  for (const auto& m : members) member_names.insert(m.name);
  std::unordered_set<std::string_view> seen;
  std::vector<std::string_view> type_keys;
  bool has_default = false;
  for (const auto* key_expr : pattern->pattern_keys) {
    auto key = key_expr->text;
    if (key == "default") {
      has_default = true;
      continue;
    }
    if (IsTypeKey(key, target.typedefs)) {
      type_keys.push_back(key);
      continue;
    }
    if (!member_names.count(key)) {
      target.diag.Error(target.loc,
                        std::format("'{}' is not a member of the struct", key),
                        Subclause("10.9.2"));
    }
    if (!seen.insert(key).second) {
      target.diag.Error(
          target.loc, std::format("duplicate member key '{}' in pattern", key),
          Subclause("10.9.2"));
    }
  }
  if (!has_default) CheckPatternCoverage(members, seen, type_keys, target);
}

}  // namespace

const std::vector<StructMember>* StructMembersOf(const DataType& type,
                                                 const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* t = FollowTypedefs(type, typedefs, names);
  if (t == nullptr || t->struct_members.empty()) return nullptr;
  return &t->struct_members;
}

void CheckStructPattern(const Expr* pattern,
                        const std::vector<StructMember>& members,
                        const StructPatternTarget& target) {
  if (!pattern->pattern_keys.empty()) {
    CheckPatternKeys(pattern, members, target);
    return;
  }
  // §5.10 (printed page 84): a replication sets the values for the exact
  // number of members, its multiplier times its items.
  if (PatternReplication(pattern) != nullptr) {
    auto count = PositionalItemCount(pattern);
    if (count && *count != static_cast<int64_t>(members.size())) {
      target.diag.Error(target.loc,
                        std::format("replication supplies {} values, but "
                                    "struct has {} members",
                                    *count, members.size()),
                        Subclause("5.10"));
    }
    return;
  }
  if (pattern->elements.size() != members.size()) {
    target.diag.Error(target.loc,
                      std::format("positional struct pattern has {} elements, "
                                  "but struct has {} members",
                                  pattern->elements.size(), members.size()),
                      Subclause("10.9.2"));
  }
}

void CheckStructPatternFor(const Expr* value, const DataType* target_type,
                           const StructPatternTarget& target) {
  const Expr* pattern = value;
  const std::vector<StructMember>* members = nullptr;
  if (value->kind == ExprKind::kCast &&
      value->lhs->kind == ExprKind::kAssignmentPattern) {
    // A typed pattern takes the type its prefix names (§10.9).
    pattern = value->lhs;
    auto it = target.typedefs.find(value->text);
    if (it != target.typedefs.end())
      members = StructMembersOf(it->second, target.typedefs);
  } else if (value->kind == ExprKind::kAssignmentPattern &&
             target_type != nullptr) {
    members = StructMembersOf(*target_type, target.typedefs);
  }
  if (members != nullptr) CheckStructPattern(pattern, *members, target);
}

void Elaborator::ValidateStructInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  // §10.9.1 with §5.10: a declaration with unpacked dimensions is initialized
  // by an array pattern whose elements are the structures, so the structure's
  // member count says nothing about how many elements that pattern lists;
  // reading it as a structure pattern rejected `'{'{0, 1}, '{2, 3}, '{4, 5}}`
  // for a three-element array of a two-member structure.
  if (!item->unpacked_dims.empty()) return;
  CheckStructPatternFor(item->init_expr, &item->data_type,
                        {typedefs_, item->loc, diag_});
}

}  // namespace delta
