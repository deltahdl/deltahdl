#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" || key == "time" ||
         key == "realtime" || key == "string";
}

static bool IsArrayPatternSpecial(const Expr* init) {
  if (init->repeat_count) return true;
  if (init->elements.size() == 1 &&
      init->elements[0]->kind == ExprKind::kReplicate)
    return true;
  return !init->pattern_keys.empty();
}

uint32_t ExtractLiteralWidth(std::string_view text) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      char c = text[i];
      if (c >= '0' && c <= '9') w = w * 10 + (c - '0');
    }
    if (w > 0) return w;
  }
  return 32;
}

std::optional<int64_t> ComputeDimSize(const Expr* dim) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs);
    auto right = ConstEvalInt(dim->rhs);
    if (left && right) return std::abs(*left - *right) + 1;
    return std::nullopt;
  }
  return ConstEvalInt(dim);
}

static void CheckArrayPatternDuplicateIndices(const Expr* init, SourceLoc loc,
                                              DiagEngine& diag) {
  if (init->pattern_keys.empty()) return;
  std::unordered_set<std::string_view> seen;
  for (auto key : init->pattern_keys) {
    if (key == "default" || IsTypeKeyword(key)) continue;
    if (!seen.insert(key).second) {
      diag.Error(loc,
                 std::format("duplicate index key '{}' in array pattern", key));
    }
  }
}

static void CheckArrayPatternCoverage(const ModuleItem* item, SourceLoc loc,
                                      DiagEngine& diag) {
  if (item->init_expr->pattern_keys.empty()) return;
  if (item->unpacked_dims.empty()) return;
  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;
  auto dim_size = ComputeDimSize(dim);
  if (!dim_size) return;

  bool has_default = false;
  bool has_type_key = false;
  std::unordered_set<std::string_view> index_keys;
  for (auto key : item->init_expr->pattern_keys) {
    if (key == "default") {
      has_default = true;
    } else if (IsTypeKeyword(key)) {
      has_type_key = true;
    } else {
      index_keys.insert(key);
    }
  }
  if (has_default || has_type_key) return;
  if (static_cast<int64_t>(index_keys.size()) < *dim_size) {
    diag.Error(loc, "keyed array pattern does not cover all elements");
  }
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (IsArrayPatternSpecial(item->init_expr)) {
    CheckArrayPatternDuplicateIndices(item->init_expr, item->loc, diag_);
    CheckArrayPatternCoverage(item, item->loc, diag_);
    return;
  }

  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;
  auto dim_size = ComputeDimSize(dim);
  if (!dim_size) return;

  auto count = static_cast<int64_t>(item->init_expr->elements.size());
  if (count != *dim_size) {
    diag_.Error(item->loc,
                std::format("assignment pattern has {} elements, but array "
                            "dimension requires {}",
                            count, *dim_size));
  }
}

static void CheckPatternCoverage(
    const ModuleItem* item, const std::vector<StructMember>& members,
    const std::unordered_set<std::string_view>& seen, DiagEngine& diag) {
  for (const auto& m : members) {
    if (!seen.count(m.name)) {
      diag.Error(
          item->loc,
          std::format("member '{}' not covered by assignment pattern", m.name));
      break;
    }
  }
}

static void CheckPatternKeys(const ModuleItem* item,
                             const std::vector<StructMember>& members,
                             DiagEngine& diag) {
  std::unordered_set<std::string_view> member_names;
  for (const auto& m : members) member_names.insert(m.name);
  std::unordered_set<std::string_view> seen;
  bool has_default = false;
  bool has_type_key = false;
  for (auto key : item->init_expr->pattern_keys) {
    if (key == "default") {
      has_default = true;
      continue;
    }
    if (IsTypeKeyword(key)) {
      has_type_key = true;
      continue;
    }
    if (!member_names.count(key)) {
      diag.Error(item->loc,
                 std::format("'{}' is not a member of the struct", key));
    }
    if (!seen.insert(key).second) {
      diag.Error(item->loc,
                 std::format("duplicate member key '{}' in pattern", key));
    }
  }

  if (!has_default && !has_type_key) {
    CheckPatternCoverage(item, members, seen, diag);
  }
}

void Elaborator::ValidateStructInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;

  const std::vector<StructMember>* members = nullptr;
  if (!item->data_type.struct_members.empty()) {
    members = &item->data_type.struct_members;
  } else if (item->data_type.kind == DataTypeKind::kNamed) {
    auto td = typedefs_.find(item->data_type.type_name);
    if (td != typedefs_.end() && !td->second.struct_members.empty())
      members = &td->second.struct_members;
  }
  if (!members) return;

  if (item->init_expr->pattern_keys.empty()) {
    bool is_replication =
        item->init_expr->repeat_count ||
        (item->init_expr->elements.size() == 1 &&
         item->init_expr->elements[0]->kind == ExprKind::kReplicate);
    if (is_replication) return;
    if (item->init_expr->elements.size() != members->size()) {
      diag_.Error(
          item->loc,
          std::format("positional struct pattern has {} elements, "
                      "but struct has {} members",
                      item->init_expr->elements.size(), members->size()));
    }
    return;
  }

  CheckPatternKeys(item, *members, diag_);
}

std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

std::string_view LhsBaseName(const Expr* e) {
  while (e) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
      e = e->base;
      continue;
    }
    break;
  }
  return {};
}

void CheckNbaDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && s->lhs->kind == ExprKind::kSelect) {
    auto name = LhsBaseName(s->lhs);
    if (!name.empty() && dyn_names.count(name) != 0) {
      if (s->kind == StmtKind::kNonblockingAssign) {
        diag.Error(s->range.start,
                   "nonblocking assignment to element of dynamic array");
      } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
        diag.Error(s->range.start,
                   "procedural continuous assignment to element of "
                   "dynamic array");
      }
    }
  }
  for (auto* sub : s->stmts) CheckNbaDynamicArrayTarget(sub, dyn_names, diag);
  for (auto* sub : s->fork_stmts)
    CheckNbaDynamicArrayTarget(sub, dyn_names, diag);
  CheckNbaDynamicArrayTarget(s->then_branch, dyn_names, diag);
  CheckNbaDynamicArrayTarget(s->else_branch, dyn_names, diag);
  CheckNbaDynamicArrayTarget(s->body, dyn_names, diag);
  CheckNbaDynamicArrayTarget(s->for_body, dyn_names, diag);
  for (auto& ci : s->case_items)
    CheckNbaDynamicArrayTarget(ci.body, dyn_names, diag);
}

static void CollectLhsBaseNames(
    const Expr* e, SourceLoc loc,
    std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) CollectLhsBaseNames(elem, loc, out);
    return;
  }
  auto name = LhsBaseName(e);
  if (!name.empty()) out.emplace(name, loc);
}

void CollectProcTargets(const Stmt* s,
                        std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CollectLhsBaseNames(s->lhs, s->range.start, out);
  }
  for (auto* sub : s->stmts) CollectProcTargets(sub, out);
  CollectProcTargets(s->then_branch, out);
  CollectProcTargets(s->else_branch, out);
  CollectProcTargets(s->body, out);
  CollectProcTargets(s->for_body, out);
  for (auto& ci : s->case_items) CollectProcTargets(ci.body, out);
}

void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease ||
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kDeassign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && interconnect_names.count(name)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in procedural "
                 "continuous assignment");
    }
  }
  for (auto* sub : s->stmts)
    CheckInterconnectProcContAssign(sub, interconnect_names, diag);
  CheckInterconnectProcContAssign(s->then_branch, interconnect_names, diag);
  CheckInterconnectProcContAssign(s->else_branch, interconnect_names, diag);
  CheckInterconnectProcContAssign(s->body, interconnect_names, diag);
  CheckInterconnectProcContAssign(s->for_body, interconnect_names, diag);
  for (auto& ci : s->case_items)
    CheckInterconnectProcContAssign(ci.body, interconnect_names, diag);
}

void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS");
  }
  for (auto* sub : s->stmts) CheckProceduralAssignLhs(sub, diag);
  for (auto* sub : s->fork_stmts) CheckProceduralAssignLhs(sub, diag);
  CheckProceduralAssignLhs(s->then_branch, diag);
  CheckProceduralAssignLhs(s->else_branch, diag);
  CheckProceduralAssignLhs(s->body, diag);
  CheckProceduralAssignLhs(s->for_body, diag);
  for (auto& ci : s->case_items) CheckProceduralAssignLhs(ci.body, diag);
}

static void CheckForceLhsOperand(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements)
      CheckForceLhsOperand(el, net_names, nettype_net_names, loc, diag);
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    auto base_name = LhsBaseName(e);
    if (base_name.empty()) return;
    if (nettype_net_names.count(base_name) != 0) {
      diag.Error(loc,
                 "bit-select or part-select of a net with a user-defined "
                 "nettype is not a legal force LHS");
    } else if (net_names.count(base_name) == 0) {
      diag.Error(loc,
                 "bit-select or part-select of a variable is not a "
                 "legal force LHS");
    }
  }
}

void CheckForceLhs(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce && s->lhs) {
    CheckForceLhsOperand(s->lhs, net_names, nettype_net_names, s->range.start,
                         diag);
  }
  for (auto* sub : s->stmts)
    CheckForceLhs(sub, net_names, nettype_net_names, diag);
  for (auto* sub : s->fork_stmts)
    CheckForceLhs(sub, net_names, nettype_net_names, diag);
  CheckForceLhs(s->then_branch, net_names, nettype_net_names, diag);
  CheckForceLhs(s->else_branch, net_names, nettype_net_names, diag);
  CheckForceLhs(s->body, net_names, nettype_net_names, diag);
  CheckForceLhs(s->for_body, net_names, nettype_net_names, diag);
  for (auto& ci : s->case_items)
    CheckForceLhs(ci.body, net_names, nettype_net_names, diag);
}

bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return names.count(e->text) > 0;
  if (ExprUsesInterconnect(e->lhs, names)) return true;
  if (ExprUsesInterconnect(e->rhs, names)) return true;
  if (ExprUsesInterconnect(e->condition, names)) return true;
  if (ExprUsesInterconnect(e->true_expr, names)) return true;
  if (ExprUsesInterconnect(e->false_expr, names)) return true;
  if (ExprUsesInterconnect(e->base, names)) return true;
  for (auto* el : e->elements)
    if (ExprUsesInterconnect(el, names)) return true;
  return false;
}

bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (!name.empty()) {
    auto it = types.find(name);
    if (it != types.end() && IsRealType(it->second)) {
      diag.Error(e->range.start, "bit-select on real type is illegal");
      return;
    }
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start, "real type used as index is illegal");
  }
}

void CheckRealSelect(const Expr* e, const TypeMap& types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, diag);
  }
  CheckRealSelect(e->lhs, types, diag);
  CheckRealSelect(e->rhs, types, diag);
  CheckRealSelect(e->base, types, diag);
  CheckRealSelect(e->index, types, diag);
}

using NameSet = std::unordered_set<std::string_view>;

static void CheckScalarSelectNode(const Expr* e, const NameSet& scalars,
                                  DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (name.empty()) return;
  if (scalars.count(name) != 0)
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal");
}

void CheckScalarSelect(const Expr* e, const NameSet& scalars,
                       DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckScalarSelectNode(e, scalars, diag);
  CheckScalarSelect(e->lhs, scalars, diag);
  CheckScalarSelect(e->rhs, scalars, diag);
  CheckScalarSelect(e->base, scalars, diag);
  CheckScalarSelect(e->index, scalars, diag);
}

static void CheckIndexedPartSelectWidthNode(const Expr* e, DiagEngine& diag) {
  if (!e->index_end) return;
  if (!e->is_part_select_plus && !e->is_part_select_minus) return;
  auto width = ConstEvalInt(e->index_end);
  if (!width.has_value()) {
    diag.Error(e->range.start,
               "indexed part-select width must be a constant expression");
    return;
  }
  // §11.5.1 requires the width of an indexed part-select to be positive.
  if (*width <= 0)
    diag.Error(e->range.start,
               "indexed part-select width must be a positive constant");
}

void CheckIndexedPartSelectWidth(const Expr* e, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckIndexedPartSelectWidthNode(e, diag);
  CheckIndexedPartSelectWidth(e->lhs, diag);
  CheckIndexedPartSelectWidth(e->rhs, diag);
  CheckIndexedPartSelectWidth(e->base, diag);
  CheckIndexedPartSelectWidth(e->index, diag);
}

void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag) {
  if (!s) return;
  CheckScalarSelect(s->lhs, scalars, diag);
  CheckScalarSelect(s->rhs, scalars, diag);
  CheckScalarSelect(s->expr, scalars, diag);
  CheckScalarSelect(s->condition, scalars, diag);
  for (auto* child : s->stmts) CheckScalarSelectStmt(child, scalars, diag);
  CheckScalarSelectStmt(s->then_branch, scalars, diag);
  CheckScalarSelectStmt(s->else_branch, scalars, diag);
  CheckScalarSelectStmt(s->body, scalars, diag);
  for (auto* fi : s->for_inits) CheckScalarSelectStmt(fi, scalars, diag);
  CheckScalarSelectStmt(s->for_body, scalars, diag);
  for (auto* fs : s->for_steps) CheckScalarSelectStmt(fs, scalars, diag);
  CheckScalarSelect(s->for_cond, scalars, diag);
  for (const auto& ci : s->case_items)
    CheckScalarSelectStmt(ci.body, scalars, diag);
  for (auto* fs : s->fork_stmts) CheckScalarSelectStmt(fs, scalars, diag);
}

void CheckIndexedPartSelectWidthStmt(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  CheckIndexedPartSelectWidth(s->lhs, diag);
  CheckIndexedPartSelectWidth(s->rhs, diag);
  CheckIndexedPartSelectWidth(s->expr, diag);
  CheckIndexedPartSelectWidth(s->condition, diag);
  for (auto* child : s->stmts) CheckIndexedPartSelectWidthStmt(child, diag);
  CheckIndexedPartSelectWidthStmt(s->then_branch, diag);
  CheckIndexedPartSelectWidthStmt(s->else_branch, diag);
  CheckIndexedPartSelectWidthStmt(s->body, diag);
  for (auto* fi : s->for_inits) CheckIndexedPartSelectWidthStmt(fi, diag);
  CheckIndexedPartSelectWidthStmt(s->for_body, diag);
  for (auto* fs : s->for_steps) CheckIndexedPartSelectWidthStmt(fs, diag);
  CheckIndexedPartSelectWidth(s->for_cond, diag);
  for (const auto& ci : s->case_items)
    CheckIndexedPartSelectWidthStmt(ci.body, diag);
  for (auto* fs : s->fork_stmts) CheckIndexedPartSelectWidthStmt(fs, diag);
}

bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprContainsIdent(e->lhs, name)) return true;
  return ExprContainsIdent(e->rhs, name);
}

bool ValidateNettypeResolutionFunction(const NettypeResolutionSig& sig) {
  // The signature shape §6.6.7 requires: returns the nettype's data type, takes
  // exactly one input argument that is a dynamic array of that type, and holds
  // no state across calls.
  if (!sig.return_type_matches_nettype) return false;
  if (!sig.single_input_argument) return false;
  if (!sig.argument_is_dynamic_array_of_type) return false;
  if (!sig.is_automatic) return false;
  // A class method is admissible only when it is static, because the resolution
  // call occurs with no class object involved.
  if (sig.is_class_method && !sig.is_static_method) return false;
  return true;
}

}  // namespace delta
