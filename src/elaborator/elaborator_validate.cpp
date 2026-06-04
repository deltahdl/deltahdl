#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);
void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" ||
         key == "time" || key == "realtime" || key == "string";
}

static bool IsArrayPatternSpecial(const Expr* init) {
  if (init->repeat_count) return true;
  if (init->elements.size() == 1 &&
      init->elements[0]->kind == ExprKind::kReplicate)
    return true;
  return !init->pattern_keys.empty();
}

static std::optional<int64_t> ComputeDimSize(const Expr* dim) {
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
      diag_.Error(item->loc,
                  std::format("positional struct pattern has {} elements, "
                              "but struct has {} members",
                              item->init_expr->elements.size(),
                              members->size()));
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

static std::string_view LhsBaseName(const Expr* e) {
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

static void CheckNbaDynamicArrayTarget(
    const Stmt* s,
    const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && s->lhs->kind == ExprKind::kSelect) {
    auto name = LhsBaseName(s->lhs);
    if (!name.empty() && dyn_names.count(name) != 0) {
      if (s->kind == StmtKind::kNonblockingAssign) {
        diag.Error(s->range.start,
                   "nonblocking assignment to element of dynamic array");
      } else if (s->kind == StmtKind::kForce ||
                 s->kind == StmtKind::kAssign) {
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

static void CollectProcTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out) {
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

static void CheckInterconnectProcContAssign(
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

static void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag) {
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
    const Expr* e,
    const std::unordered_set<std::string_view>& net_names,
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
      diag.Error(loc, "bit-select or part-select of a variable is not a "
                      "legal force LHS");
    }
  }
}

static void CheckForceLhs(
    const Stmt* s,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce && s->lhs) {
    CheckForceLhsOperand(s->lhs, net_names, nettype_net_names,
                         s->range.start, diag);
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

static bool ExprUsesInterconnect(
    const Expr* e,
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

static void CheckRealSelect(const Expr* e, const TypeMap& types,
                            DiagEngine& diag) {
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
    diag.Error(e->range.start, "bit-select or part-select of a scalar is illegal");
}

static void CheckScalarSelect(const Expr* e, const NameSet& scalars,
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

static void CheckIndexedPartSelectWidth(const Expr* e, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckIndexedPartSelectWidthNode(e, diag);
  CheckIndexedPartSelectWidth(e->lhs, diag);
  CheckIndexedPartSelectWidth(e->rhs, diag);
  CheckIndexedPartSelectWidth(e->base, diag);
  CheckIndexedPartSelectWidth(e->index, diag);
}

static void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
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

static void CheckIndexedPartSelectWidthStmt(const Stmt* s, DiagEngine& diag) {
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

static bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprContainsIdent(e->lhs, name)) return true;
  return ExprContainsIdent(e->rhs, name);
}

void Elaborator::ValidateEdgeOnReal(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kNone) continue;
    auto name = ExprIdent(ev.signal);
    if (name.empty()) continue;
    auto it = var_types_.find(name);
    if (it != var_types_.end() && IsRealType(it->second)) {
      diag_.Error(item->loc, "edge event on real type is illegal");
    }
  }
}

static bool IsChandleVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kChandle;
}

void Elaborator::ValidateChandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (IsChandleVar(item->assign_lhs, var_types_) ||
      IsChandleVar(item->assign_rhs, var_types_)) {
    diag_.Error(item->loc, "chandle cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateChandleSensitivity(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (IsChandleVar(ev.signal, var_types_)) {
      diag_.Error(item->loc, "chandle cannot appear in event expression");
    }
  }
}

static bool IsNullLiteral(const Expr* e) {
  return e && e->kind == ExprKind::kIdentifier && e->text == "null";
}

static bool IsAllowedChandleBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static void CheckChandleExpr(const Expr* e, const TypeMap& types,
                              DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ch = e->lhs && IsChandleVar(e->lhs, types);
    bool rhs_ch = e->rhs && IsChandleVar(e->rhs, types);
    if ((lhs_ch || rhs_ch) && !IsAllowedChandleBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on chandle");
    }
  }
  if (e->kind == ExprKind::kUnary && IsChandleVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on chandle");
  }
  if (e->kind == ExprKind::kPostfixUnary && IsChandleVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on chandle");
  }
  if (e->kind == ExprKind::kSelect && e->base &&
      IsChandleVar(e->base, types)) {
    diag.Error(e->range.start, "bit-select on chandle is illegal");
  }
  CheckChandleExpr(e->lhs, types, diag);
  CheckChandleExpr(e->rhs, types, diag);
  CheckChandleExpr(e->base, types, diag);
  CheckChandleExpr(e->index, types, diag);
  CheckChandleExpr(e->condition, types, diag);
  CheckChandleExpr(e->true_expr, types, diag);
  CheckChandleExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckChandleExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForChandleOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    bool lhs_ch = IsChandleVar(s->lhs, var_types_);
    bool rhs_ch = IsChandleVar(s->rhs, var_types_);
    if (lhs_ch && !rhs_ch && !IsNullLiteral(s->rhs)) {
      diag_.Error(s->range.start,
                  "chandle can only be assigned from another chandle or null");
    }
    if (!lhs_ch && rhs_ch) {
      diag_.Error(s->range.start,
                  "chandle cannot be assigned to a non-chandle variable");
    }
  }
  CheckChandleExpr(s->rhs, var_types_, diag_);
  CheckChandleExpr(s->expr, var_types_, diag_);
  CheckChandleExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForChandleOps(sub);
  WalkStmtsForChandleOps(s->then_branch);
  WalkStmtsForChandleOps(s->else_branch);
  WalkStmtsForChandleOps(s->body);
  WalkStmtsForChandleOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForChandleOps(ci.body);
}

void Elaborator::ValidateChandleOps(const ModuleDecl* decl) {
  bool has_chandle = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kChandle) {
      has_chandle = true;
      break;
    }
  }
  if (!has_chandle) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForChandleOps(item->body);
    }
  }
}

static bool IsVirtualInterfaceVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kVirtualInterface;
}

// §25.9: leftmost identifier of a (possibly hierarchical) reference, e.g. "u"
// for the defparam path u.W.
static std::string_view ReferenceRootName(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->lhs != nullptr) {
      e = e->lhs;
    } else if (e->base != nullptr) {
      e = e->base;
    } else {
      break;
    }
  }
  return {};
}

static bool ExprUsesVirtualInterface(const Expr* e, const TypeMap& types) {
  if (!e) return false;
  if (IsVirtualInterfaceVar(e, types)) return true;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      IsVirtualInterfaceVar(e->lhs, types)) {
    return true;
  }
  if (ExprUsesVirtualInterface(e->lhs, types)) return true;
  if (ExprUsesVirtualInterface(e->rhs, types)) return true;
  if (ExprUsesVirtualInterface(e->base, types)) return true;
  if (ExprUsesVirtualInterface(e->index, types)) return true;
  if (ExprUsesVirtualInterface(e->condition, types)) return true;
  if (ExprUsesVirtualInterface(e->true_expr, types)) return true;
  if (ExprUsesVirtualInterface(e->false_expr, types)) return true;
  for (const auto* elem : e->elements) {
    if (ExprUsesVirtualInterface(elem, types)) return true;
  }
  return false;
}

void Elaborator::ValidateVirtualInterfaceContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (ExprUsesVirtualInterface(item->assign_lhs, var_types_) ||
      ExprUsesVirtualInterface(item->assign_rhs, var_types_)) {
    diag_.Error(item->loc,
                "virtual interface cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateVirtualInterfaceSensitivity(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ExprUsesVirtualInterface(ev.signal, var_types_)) {
      diag_.Error(item->loc,
                  "virtual interface cannot appear in event expression");
    }
  }
}

static bool IsAllowedVirtualInterfaceBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

static void CheckVirtualInterfaceExpr(const Expr* e, const TypeMap& types,
                                      DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_vi = e->lhs && IsVirtualInterfaceVar(e->lhs, types);
    bool rhs_vi = e->rhs && IsVirtualInterfaceVar(e->rhs, types);
    if ((lhs_vi || rhs_vi) && !IsAllowedVirtualInterfaceBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on virtual interface");
    }
  }
  if (e->kind == ExprKind::kUnary && IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start,
               "operator is not allowed on virtual interface");
  }
  if (e->kind == ExprKind::kPostfixUnary &&
      IsVirtualInterfaceVar(e->lhs, types)) {
    diag.Error(e->range.start,
               "operator is not allowed on virtual interface");
  }
  if (e->kind == ExprKind::kSelect && e->base &&
      IsVirtualInterfaceVar(e->base, types)) {
    diag.Error(e->range.start, "bit-select on virtual interface is illegal");
  }
  CheckVirtualInterfaceExpr(e->lhs, types, diag);
  CheckVirtualInterfaceExpr(e->rhs, types, diag);
  CheckVirtualInterfaceExpr(e->base, types, diag);
  CheckVirtualInterfaceExpr(e->index, types, diag);
  CheckVirtualInterfaceExpr(e->condition, types, diag);
  CheckVirtualInterfaceExpr(e->true_expr, types, diag);
  CheckVirtualInterfaceExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckVirtualInterfaceExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForVirtualInterfaceOps(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    bool lhs_vi = IsVirtualInterfaceVar(s->lhs, var_types_);
    bool rhs_vi = IsVirtualInterfaceVar(s->rhs, var_types_);
    auto rhs_name = ExprIdent(s->rhs);
    bool rhs_is_iface_inst =
        !rhs_name.empty() && interface_inst_types_.count(rhs_name) != 0;
    if (lhs_vi && !rhs_vi && !rhs_is_iface_inst && !IsNullLiteral(s->rhs)) {
      diag_.Error(s->range.start,
                  "virtual interface can only be assigned from another "
                  "virtual interface, an interface instance, or null");
    }
    if (lhs_vi && rhs_vi) {
      auto lhs_name = ExprIdent(s->lhs);
      auto lit = vi_var_interface_types_.find(lhs_name);
      auto rit = vi_var_interface_types_.find(rhs_name);
      if (lit != vi_var_interface_types_.end() &&
          rit != vi_var_interface_types_.end() && lit->second != rit->second) {
        diag_.Error(s->range.start,
                    "virtual interface assignment between incompatible "
                    "interface types");
      }
      auto lmp = vi_var_modports_.find(lhs_name);
      auto rmp = vi_var_modports_.find(rhs_name);
      bool lhs_has_mp =
          lmp != vi_var_modports_.end() && !lmp->second.empty();
      bool rhs_has_mp =
          rmp != vi_var_modports_.end() && !rmp->second.empty();
      if (!lhs_has_mp && rhs_has_mp) {
        diag_.Error(s->range.start,
                    "virtual interface with modport cannot be assigned to "
                    "virtual interface without modport");
      } else if (lhs_has_mp && rhs_has_mp && lmp->second != rmp->second) {
        diag_.Error(s->range.start,
                    "virtual interface modports do not match");
      }
      // §25.9: the actual parameter values shall match for two virtual
      // interfaces to be of the same type and assignment compatible.
      auto lpv = vi_var_param_values_.find(lhs_name);
      auto rpv = vi_var_param_values_.find(rhs_name);
      if (lpv != vi_var_param_values_.end() &&
          rpv != vi_var_param_values_.end() && lpv->second != rpv->second) {
        diag_.Error(s->range.start,
                    "virtual interface parameter values do not match");
      }
    }
    if (lhs_vi && rhs_is_iface_inst) {
      auto lhs_name = ExprIdent(s->lhs);
      auto lit = vi_var_interface_types_.find(lhs_name);
      auto iit = interface_inst_types_.find(rhs_name);
      if (lit != vi_var_interface_types_.end() &&
          iit != interface_inst_types_.end() && lit->second != iit->second) {
        diag_.Error(s->range.start,
                    "virtual interface assignment from interface instance of "
                    "incompatible type");
      }
      // §25.9: the actual parameter values of the interface instance shall
      // match those of the virtual interface.
      auto lpv = vi_var_param_values_.find(lhs_name);
      auto ipv = interface_inst_param_values_.find(rhs_name);
      if (lpv != vi_var_param_values_.end() &&
          ipv != interface_inst_param_values_.end() &&
          lpv->second != ipv->second) {
        diag_.Error(s->range.start,
                    "virtual interface parameter values do not match the "
                    "interface instance");
      }
      // §25.9: it is illegal to assign an interface instance to a virtual
      // interface when a defparam targeting that instance is declared outside
      // the interface.
      if (vi_external_defparam_insts_.count(rhs_name)) {
        diag_.Error(s->range.start,
                    "interface instance targeted by a defparam declared "
                    "outside the interface cannot be assigned to a virtual "
                    "interface");
      }
    }
    if (!lhs_vi && rhs_vi) {
      diag_.Error(s->range.start,
                  "virtual interface cannot be assigned to a non-virtual-"
                  "interface variable");
    }
  }
  CheckVirtualInterfaceExpr(s->rhs, var_types_, diag_);
  CheckVirtualInterfaceExpr(s->expr, var_types_, diag_);
  CheckVirtualInterfaceExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForVirtualInterfaceOps(sub);
  WalkStmtsForVirtualInterfaceOps(s->then_branch);
  WalkStmtsForVirtualInterfaceOps(s->else_branch);
  WalkStmtsForVirtualInterfaceOps(s->body);
  WalkStmtsForVirtualInterfaceOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForVirtualInterfaceOps(ci.body);
}

void Elaborator::ValidateVirtualInterfaceOps(const ModuleDecl* decl) {
  bool has_vi = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kVirtualInterface) {
      has_vi = true;
      break;
    }
  }
  if (!has_vi) return;
  // §25.9: a defparam declared in this scope (i.e. outside the interface)
  // targeting an interface instance taints that instance for assignment to a
  // virtual interface.
  vi_external_defparam_insts_.clear();
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& assign : item->defparam_assigns) {
      auto root = ReferenceRootName(assign.first);
      if (!root.empty() && interface_inst_types_.count(root)) {
        vi_external_defparam_insts_.insert(root);
      }
    }
  }
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForVirtualInterfaceOps(item->body);
    }
  }
}

static bool IsEventVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kEvent;
}

// §15.5.5.3: an event variable may be compared against another event or null
// only with equality (==), inequality (!=), case equality (===), or case
// inequality (!==). The four case/logical equality operators are the only
// binary operators allowed on an event operand.
static bool IsAllowedEventBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

// §15.5.5.3: reject any operator applied to an event variable other than the
// permitted comparisons (and the implicit Boolean test, which uses the event
// directly rather than through an operator node). Arithmetic, relational,
// bitwise, unary, and select operators on events are all illegal.
static void CheckEventExpr(const Expr* e, const TypeMap& types,
                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary) {
    bool lhs_ev = e->lhs && IsEventVar(e->lhs, types);
    bool rhs_ev = e->rhs && IsEventVar(e->rhs, types);
    if ((lhs_ev || rhs_ev) && !IsAllowedEventBinaryOp(e->op)) {
      diag.Error(e->range.start, "operator is not allowed on event variable");
    }
  }
  if (e->kind == ExprKind::kUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on event variable");
  }
  if (e->kind == ExprKind::kPostfixUnary && IsEventVar(e->lhs, types)) {
    diag.Error(e->range.start, "operator is not allowed on event variable");
  }
  CheckEventExpr(e->lhs, types, diag);
  CheckEventExpr(e->rhs, types, diag);
  CheckEventExpr(e->base, types, diag);
  CheckEventExpr(e->index, types, diag);
  CheckEventExpr(e->condition, types, diag);
  CheckEventExpr(e->true_expr, types, diag);
  CheckEventExpr(e->false_expr, types, diag);
  for (const auto* elem : e->elements) {
    CheckEventExpr(elem, types, diag);
  }
}

void Elaborator::WalkStmtsForEventOps(const Stmt* s) {
  if (!s) return;
  // Event-control event lists (s->events) are not operator expressions and are
  // intentionally left untouched here; only value expressions are inspected.
  CheckEventExpr(s->rhs, var_types_, diag_);
  CheckEventExpr(s->expr, var_types_, diag_);
  CheckEventExpr(s->condition, var_types_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForEventOps(sub);
  WalkStmtsForEventOps(s->then_branch);
  WalkStmtsForEventOps(s->else_branch);
  WalkStmtsForEventOps(s->body);
  WalkStmtsForEventOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForEventOps(ci.body);
}

void Elaborator::ValidateEventOps(const ModuleDecl* decl) {
  bool has_event = false;
  for (const auto& [name, kind] : var_types_) {
    if (kind == DataTypeKind::kEvent) {
      has_event = true;
      break;
    }
  }
  if (!has_event) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForEventOps(item->body);
    }
  }
}

namespace {

using VifTypeMap = std::unordered_map<std::string_view, std::string_view>;
using VifModportMap = std::unordered_map<std::string_view, std::string_view>;

std::string_view ResolveVifInterfaceType(const DataType& dt,
                                         const TypedefMap& typedefs) {
  if (dt.kind == DataTypeKind::kVirtualInterface) return dt.type_name;
  if (dt.kind == DataTypeKind::kNamed) {
    auto it = typedefs.find(dt.type_name);
    if (it != typedefs.end() &&
        it->second.kind == DataTypeKind::kVirtualInterface) {
      return it->second.type_name;
    }
  }
  return {};
}

std::string_view ResolveVifModport(const DataType& dt,
                                   const TypedefMap& typedefs) {
  if (dt.kind == DataTypeKind::kVirtualInterface) return dt.modport_name;
  if (dt.kind == DataTypeKind::kNamed) {
    auto it = typedefs.find(dt.type_name);
    if (it != typedefs.end() &&
        it->second.kind == DataTypeKind::kVirtualInterface) {
      return it->second.modport_name;
    }
  }
  return {};
}

const ModuleDecl* FindInterfaceDeclByName(const CompilationUnit* unit,
                                          std::string_view name) {
  if (!unit) return nullptr;
  for (const auto* i : unit->interfaces) {
    if (i && i->name == name) return i;
  }
  for (const auto* m : unit->modules) {
    if (m && m->name == name &&
        m->decl_kind == ModuleDeclKind::kInterface) {
      return m;
    }
  }
  return nullptr;
}

void CheckVifClockingExpr(const Expr* e, const VifTypeMap& vifs,
                          const VifModportMap& vif_mps,
                          const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess && e->lhs->lhs &&
      e->lhs->lhs->kind == ExprKind::kIdentifier) {
    auto vif_it = vifs.find(e->lhs->lhs->text);
    if (vif_it != vifs.end()) {
      std::string_view block_name;
      if (e->lhs->rhs && e->lhs->rhs->kind == ExprKind::kIdentifier) {
        block_name = e->lhs->rhs->text;
      } else if (!e->lhs->text.empty()) {
        block_name = e->lhs->text;
      }
      std::string_view sig_name;
      if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
        sig_name = e->rhs->text;
      } else if (!e->text.empty()) {
        sig_name = e->text;
      }
      const auto* iface = FindInterfaceDeclByName(unit, vif_it->second);
      if (iface && !block_name.empty()) {
        std::string_view modport_name;
        auto mp_it = vif_mps.find(e->lhs->lhs->text);
        if (mp_it != vif_mps.end()) modport_name = mp_it->second;

        const ModportDecl* modport = nullptr;
        if (!modport_name.empty()) {
          for (const auto* mp : iface->modports) {
            if (mp && mp->name == modport_name) {
              modport = mp;
              break;
            }
          }
        }

        const ModuleItem* cb_item = nullptr;
        bool member_exists = false;
        for (const auto* it : iface->items) {
          if (it->kind == ModuleItemKind::kClockingBlock &&
              it->name == block_name) {
            cb_item = it;
            break;
          }
          if ((it->kind == ModuleItemKind::kVarDecl ||
               it->kind == ModuleItemKind::kNetDecl) &&
              it->name == block_name) {
            member_exists = true;
          }
        }

        if (cb_item && modport) {
          bool clocking_in_modport = false;
          for (const auto& p : modport->ports) {
            if (p.is_clocking && p.name == block_name) {
              clocking_in_modport = true;
              break;
            }
          }
          if (!clocking_in_modport) {
            diag.Error(
                e->range.start,
                std::format(
                    "clocking block '{}' is not accessible through modport "
                    "'{}' of interface '{}'",
                    block_name, modport_name, vif_it->second));
            cb_item = nullptr;
          }
        }

        if (!cb_item && !member_exists) {
          diag.Error(e->range.start,
                     std::format("'{}' is not a clocking block or member of "
                                 "interface '{}'",
                                 block_name, vif_it->second));
        } else if (cb_item && !sig_name.empty()) {
          bool signal_found = false;
          for (const auto& sig : cb_item->clocking_signals) {
            if (sig.name == sig_name) {
              signal_found = true;
              break;
            }
          }
          if (!signal_found) {
            diag.Error(e->range.start,
                       std::format(
                           "'{}' is not a signal of clocking block '{}' in "
                           "interface '{}'",
                           sig_name, block_name, vif_it->second));
          }
        }
      }
    }
  }
  CheckVifClockingExpr(e->lhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->rhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->base, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->index, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->condition, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->true_expr, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->false_expr, vifs, vif_mps, unit, diag);
  for (const auto* elem : e->elements) {
    CheckVifClockingExpr(elem, vifs, vif_mps, unit, diag);
  }
  for (const auto* arg : e->args) {
    CheckVifClockingExpr(arg, vifs, vif_mps, unit, diag);
  }
}

void WalkStmtsForVifClocking(const Stmt* s, const VifTypeMap& vifs,
                             const VifModportMap& vif_mps,
                             const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVifClockingExpr(s->lhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->rhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->expr, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->condition, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->var_init, vifs, vif_mps, unit, diag);
  for (const auto* sub : s->stmts)
    WalkStmtsForVifClocking(sub, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->then_branch, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->else_branch, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->body, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->for_body, vifs, vif_mps, unit, diag);
  for (auto& ci : s->case_items) {
    WalkStmtsForVifClocking(ci.body, vifs, vif_mps, unit, diag);
  }
}

}

void Elaborator::ValidateArrayOfVifInitStmt(const Stmt* s) {
  if (!s || s->kind != StmtKind::kVarDecl) return;
  if (!s->var_init) return;
  if (s->var_init->kind != ExprKind::kAssignmentPattern) return;
  std::string_view iface_type =
      ResolveVifInterfaceType(s->var_decl_type, typedefs_);
  if (iface_type.empty()) return;
  if (s->var_unpacked_dims.empty()) return;

  auto size_opt = ComputeDimSize(s->var_unpacked_dims.front());
  if (size_opt && static_cast<int64_t>(s->var_init->elements.size()) !=
                      *size_opt) {
    diag_.Error(
        s->var_init->range.start,
        std::format(
            "array-of-virtual-interface initializer has {} elements but "
            "'{}' has size {}",
            s->var_init->elements.size(), s->var_name, *size_opt));
  }

  for (const auto* elem : s->var_init->elements) {
    if (!elem) continue;
    if (elem->kind != ExprKind::kIdentifier) continue;
    auto inst_it = interface_inst_types_.find(elem->text);
    if (inst_it != interface_inst_types_.end()) {
      if (inst_it->second != iface_type) {
        diag_.Error(
            elem->range.start,
            std::format(
                "interface instance '{}' of type '{}' is not compatible "
                "with virtual interface element type '{}'",
                elem->text, inst_it->second, iface_type));
      }
      continue;
    }
    auto vif_it = vi_var_interface_types_.find(elem->text);
    if (vif_it != vi_var_interface_types_.end()) {
      if (vif_it->second != iface_type) {
        diag_.Error(
            elem->range.start,
            std::format(
                "virtual interface '{}' of type '{}' is not compatible "
                "with element type '{}'",
                elem->text, vif_it->second, iface_type));
      }
    }
  }
}

static void WalkStmtsForArrayOfVifInit(const Stmt* s, Elaborator* elab) {
  if (!s) return;
  elab->ValidateArrayOfVifInitStmt(s);
  for (const auto* sub : s->stmts) WalkStmtsForArrayOfVifInit(sub, elab);
  WalkStmtsForArrayOfVifInit(s->then_branch, elab);
  WalkStmtsForArrayOfVifInit(s->else_branch, elab);
  WalkStmtsForArrayOfVifInit(s->body, elab);
  WalkStmtsForArrayOfVifInit(s->for_body, elab);
  for (auto& ci : s->case_items) WalkStmtsForArrayOfVifInit(ci.body, elab);
}

void Elaborator::WalkStmtsForVirtualInterfaceClocking(const Stmt* s) {
  WalkStmtsForArrayOfVifInit(s, this);
}

void Elaborator::ValidateVirtualInterfaceClocking(const ModuleDecl* decl) {
  VifTypeMap module_vifs = vi_var_interface_types_;
  VifModportMap module_mps = vi_var_modports_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      VifTypeMap scoped = module_vifs;
      VifModportMap scoped_mps = module_mps;
      for (const auto& a : item->func_args) {
        auto t = ResolveVifInterfaceType(a.data_type, typedefs_);
        if (!t.empty()) {
          scoped[a.name] = t;
          scoped_mps[a.name] = ResolveVifModport(a.data_type, typedefs_);
        }
      }
      if (item->body) {
        WalkStmtsForVifClocking(item->body, scoped, scoped_mps, unit_, diag_);
        WalkStmtsForVirtualInterfaceClocking(item->body);
      }
    } else {
      bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                     item->kind == ModuleItemKind::kAlwaysCombBlock ||
                     item->kind == ModuleItemKind::kAlwaysFFBlock ||
                     item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                     item->kind == ModuleItemKind::kInitialBlock ||
                     item->kind == ModuleItemKind::kFinalBlock;
      if (is_proc && item->body) {
        WalkStmtsForVifClocking(item->body, module_vifs, module_mps, unit_,
                                diag_);
        WalkStmtsForVirtualInterfaceClocking(item->body);
      }
    }
  }
}

namespace {

using IfacePortTypeMap =
    std::unordered_map<std::string_view, std::string_view>;
using IfacePortModportMap =
    std::unordered_map<std::string_view, std::string_view>;

const ModuleDecl* LookupInterfaceDecl(const CompilationUnit* unit,
                                      std::string_view name) {
  if (!unit) return nullptr;
  for (const auto* i : unit->interfaces) {
    if (i && i->name == name) return i;
  }
  for (const auto* m : unit->modules) {
    if (m && m->name == name &&
        m->decl_kind == ModuleDeclKind::kInterface) {
      return m;
    }
  }
  return nullptr;
}

bool IsListableInModport(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kNetDecl:
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kClockingBlock:
      return true;
    default:
      return false;
  }
}

const ModuleItem* FindInterfaceItemByName(const ModuleDecl* iface,
                                          std::string_view name) {
  if (!iface) return nullptr;
  for (const auto* it : iface->items) {
    if (it && it->name == name) return it;
  }
  return nullptr;
}

bool ModportListsMember(const ModportDecl* mp, std::string_view name) {
  if (!mp) return false;
  for (const auto& p : mp->ports) {
    if (p.name == name) return true;
  }
  return false;
}

const ModportDecl* FindModport(const ModuleDecl* iface,
                               std::string_view modport_name) {
  if (!iface || modport_name.empty()) return nullptr;
  for (const auto* mp : iface->modports) {
    if (mp && mp->name == modport_name) return mp;
  }
  return nullptr;
}

void CheckInterfaceObjectAccessExpr(const Expr* e,
                                    const IfacePortTypeMap& iface_ports,
                                    const IfacePortModportMap& port_mps,
                                    const VifTypeMap& vifs,
                                    const VifModportMap& vif_mps,
                                    const CompilationUnit* unit,
                                    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs &&
      e->rhs->kind == ExprKind::kIdentifier) {
    auto base_name = e->lhs->text;
    auto member_name = e->rhs->text;

    std::string_view iface_type;
    std::string_view modport_name;
    bool bound = false;

    auto pit = iface_ports.find(base_name);
    if (pit != iface_ports.end()) {
      iface_type = pit->second;
      auto mp_it = port_mps.find(base_name);
      if (mp_it != port_mps.end()) modport_name = mp_it->second;
      bound = true;
    } else {
      auto vit = vifs.find(base_name);
      if (vit != vifs.end()) {
        iface_type = vit->second;
        auto mp_it = vif_mps.find(base_name);
        if (mp_it != vif_mps.end()) modport_name = mp_it->second;
        bound = true;
      }
    }

    if (bound && !modport_name.empty() && !member_name.empty()) {
      const auto* iface = LookupInterfaceDecl(unit, iface_type);
      const auto* mp = FindModport(iface, modport_name);
      if (iface && mp) {
        const auto* member = FindInterfaceItemByName(iface, member_name);
        if (member && IsListableInModport(member->kind) &&
            member->kind != ModuleItemKind::kClockingBlock &&
            !ModportListsMember(mp, member_name)) {
          diag.Error(
              e->range.start,
              std::format(
                  "'{}' is not accessible through modport '{}' of interface "
                  "'{}'",
                  member_name, modport_name, iface_type));
        }
      }
    }
  }
  CheckInterfaceObjectAccessExpr(e->lhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->rhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->base, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->index, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->condition, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(e->true_expr, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(e->false_expr, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  for (const auto* elem : e->elements) {
    CheckInterfaceObjectAccessExpr(elem, iface_ports, port_mps, vifs, vif_mps,
                                   unit, diag);
  }
  for (const auto* arg : e->args) {
    CheckInterfaceObjectAccessExpr(arg, iface_ports, port_mps, vifs, vif_mps,
                                   unit, diag);
  }
}

void WalkStmtsForInterfaceObjectAccess(const Stmt* s,
                                       const IfacePortTypeMap& iface_ports,
                                       const IfacePortModportMap& port_mps,
                                       const VifTypeMap& vifs,
                                       const VifModportMap& vif_mps,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  if (!s) return;
  CheckInterfaceObjectAccessExpr(s->lhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->rhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->expr, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->condition, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(s->var_init, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  for (const auto* sub : s->stmts) {
    WalkStmtsForInterfaceObjectAccess(sub, iface_ports, port_mps, vifs, vif_mps,
                                      unit, diag);
  }
  WalkStmtsForInterfaceObjectAccess(s->then_branch, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->else_branch, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->body, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->for_body, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  for (auto& ci : s->case_items) {
    WalkStmtsForInterfaceObjectAccess(ci.body, iface_ports, port_mps, vifs,
                                      vif_mps, unit, diag);
  }
}

}

void Elaborator::ValidateInterfaceObjectAccess(const ModuleDecl* decl) {
  if (!decl) return;

  IfacePortTypeMap iface_ports;
  IfacePortModportMap port_mps;
  for (const auto& port : decl->ports) {
    if (port.name.empty()) continue;
    if (port.data_type.kind != DataTypeKind::kNamed) continue;
    const auto* ifc = FindModule(port.data_type.type_name);
    if (!ifc || ifc->decl_kind != ModuleDeclKind::kInterface) continue;
    iface_ports[port.name] = port.data_type.type_name;
    port_mps[port.name] = port.data_type.modport_name;
  }

  if (iface_ports.empty() && vi_var_interface_types_.empty()) return;

  VifTypeMap module_vifs = vi_var_interface_types_;
  VifModportMap module_mps = vi_var_modports_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      VifTypeMap scoped = module_vifs;
      VifModportMap scoped_mps = module_mps;
      for (const auto& a : item->func_args) {
        auto t = ResolveVifInterfaceType(a.data_type, typedefs_);
        if (!t.empty()) {
          scoped[a.name] = t;
          scoped_mps[a.name] = ResolveVifModport(a.data_type, typedefs_);
        }
      }
      if (item->body) {
        WalkStmtsForInterfaceObjectAccess(item->body, iface_ports, port_mps,
                                          scoped, scoped_mps, unit_, diag_);
      }
    } else if (item->kind == ModuleItemKind::kContAssign) {
      CheckInterfaceObjectAccessExpr(item->assign_lhs, iface_ports, port_mps,
                                     module_vifs, module_mps, unit_, diag_);
      CheckInterfaceObjectAccessExpr(item->assign_rhs, iface_ports, port_mps,
                                     module_vifs, module_mps, unit_, diag_);
    } else {
      bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                     item->kind == ModuleItemKind::kAlwaysCombBlock ||
                     item->kind == ModuleItemKind::kAlwaysFFBlock ||
                     item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                     item->kind == ModuleItemKind::kInitialBlock ||
                     item->kind == ModuleItemKind::kFinalBlock;
      if (is_proc && item->body) {
        WalkStmtsForInterfaceObjectAccess(item->body, iface_ports, port_mps,
                                          module_vifs, module_mps, unit_,
                                          diag_);
      }
    }
  }
}

void Elaborator::ValidateInterconnectContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;

  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier &&
      interconnect_names_.count(item->assign_lhs->text)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in continuous assignment");
  }

  if (ExprUsesInterconnect(item->assign_rhs, interconnect_names_)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in expression");
  }
}

static void CheckLhsPatternNamedKeys(const Expr* lhs, DiagEngine& diag) {
  if (!lhs) return;
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast && pat->lhs)
    pat = pat->lhs;
  if (pat->kind == ExprKind::kAssignmentPattern &&
      !pat->pattern_keys.empty()) {
    diag.Error(lhs->range.start,
               "LHS assignment pattern shall use positional notation only");
  }
}

static void WalkStmtsForLhsPatternKeys(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternNamedKeys(s->lhs, diag);
  }
  for (auto* sub : s->stmts) WalkStmtsForLhsPatternKeys(sub, diag);
  WalkStmtsForLhsPatternKeys(s->then_branch, diag);
  WalkStmtsForLhsPatternKeys(s->else_branch, diag);
  WalkStmtsForLhsPatternKeys(s->body, diag);
  WalkStmtsForLhsPatternKeys(s->for_body, diag);
  for (auto& ci : s->case_items) WalkStmtsForLhsPatternKeys(ci.body, diag);
}

// §10.9: a positional assignment pattern on the LHS shall hold the same number
// of bits as the RHS supplies. Fire only when both sides have statically known
// widths so that unrelated diagnostics keep their primacy.
static void CheckLhsPatternWidthSum(const Expr* lhs, const Expr* rhs,
                                    const RtlirModule* mod,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  if (!lhs || !rhs) return;
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast && pat->lhs) pat = pat->lhs;
  if (pat->kind != ExprKind::kAssignmentPattern) return;
  if (!pat->pattern_keys.empty()) return;
  if (pat->elements.empty()) return;

  uint32_t sum = 0;
  for (const auto* elem : pat->elements) {
    uint32_t w = LookupLhsWidth(elem, mod);
    if (w == 0) return;
    sum += w;
  }
  uint32_t rhs_w = InferExprWidth(rhs, typedefs);
  if (rhs_w == 0) return;
  if (sum == rhs_w) return;

  diag.Error(lhs->range.start,
             std::format("LHS assignment pattern needs {} bits but RHS "
                         "supplies {} bits",
                         sum, rhs_w));
}

static void WalkStmtsForLhsPatternWidths(const Stmt* s,
                                         const RtlirModule* mod,
                                         const TypedefMap& typedefs,
                                         DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternWidthSum(s->lhs, s->rhs, mod, typedefs, diag);
  }
  for (auto* sub : s->stmts)
    WalkStmtsForLhsPatternWidths(sub, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->then_branch, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->else_branch, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->body, mod, typedefs, diag);
  WalkStmtsForLhsPatternWidths(s->for_body, mod, typedefs, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForLhsPatternWidths(ci.body, mod, typedefs, diag);
}

void Elaborator::ValidateLhsPatternWidths(const ModuleDecl* decl,
                                          const RtlirModule* mod) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForLhsPatternWidths(item->body, mod, typedefs_, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckLhsPatternWidthSum(item->assign_lhs, item->assign_rhs, mod,
                              typedefs_, diag_);
    }
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);

    CheckInterconnectProcContAssign(item->body, interconnect_names_, diag_);
    CheckProceduralAssignLhs(item->body, diag_);

    CheckForceLhs(item->body, net_names_, nettype_net_names_, diag_);

    WalkStmtsForLhsPatternKeys(item->body, diag_);
  }
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateVirtualInterfaceContAssign(item);
  ValidateVirtualInterfaceSensitivity(item);
  ValidateInterconnectContAssign(item);
  ValidateClassHandleContAssign(item);

  if (item->kind == ModuleItemKind::kNetDecl &&
      (item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      !item->init_expr) {
    diag_.Error(item->loc,
                "drive strength on net declaration requires an assignment");
  }

  if ((item->kind == ModuleItemKind::kNetDecl ||
       item->kind == ModuleItemKind::kContAssign ||
       item->kind == ModuleItemKind::kGateInst ||
       item->kind == ModuleItemKind::kUdpInst) &&
      item->drive_strength0 == 1 && item->drive_strength1 == 1) {
    diag_.Error(item->loc, "drive strength (highz0, highz1) is illegal");
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
    CheckScalarSelect(item->assign_rhs, scalar_var_names_, diag_);
    CheckScalarSelect(item->assign_lhs, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidth(item->assign_rhs, diag_);
    CheckIndexedPartSelectWidth(item->assign_lhs, diag_);
  }
  if (is_proc && item->body) {
    CheckScalarSelectStmt(item->body, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidthStmt(item->body, diag_);
  }
}

// §12.6: "A constant expression pattern shall be of integral type." Real and
// string literals are the constant expressions that are not integral.
static bool IsNonIntegralConstantPattern(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kRealLiteral) return true;
  if (e->kind == ExprKind::kStringLiteral) return true;
  return false;
}

static void CheckMatchesPattern(const Expr* pat, DiagEngine& diag) {
  if (!pat) return;
  // A `pattern &&& filter_expression` (§12.6.1) wraps the actual pattern on the
  // left; the filter on the right is an ordinary expression, not a pattern.
  const Expr* p = pat;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    p = p->lhs;
  }
  if (IsNonIntegralConstantPattern(p)) {
    diag.Error(p->range.start,
               "constant expression pattern shall be of integral type");
  }
}

static void WalkExprForMatchesOp(const Expr* e, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kKwMatches) {
    CheckMatchesPattern(e->rhs, diag);
  }
  WalkExprForMatchesOp(e->lhs, diag);
  WalkExprForMatchesOp(e->rhs, diag);
  WalkExprForMatchesOp(e->condition, diag);
  WalkExprForMatchesOp(e->true_expr, diag);
  WalkExprForMatchesOp(e->false_expr, diag);
  WalkExprForMatchesOp(e->base, diag);
  WalkExprForMatchesOp(e->index, diag);
  WalkExprForMatchesOp(e->index_end, diag);
  for (auto* a : e->args) WalkExprForMatchesOp(a, diag);
  for (auto* x : e->elements) WalkExprForMatchesOp(x, diag);
}

static void WalkStmtForMatchesPattern(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kCase && s->case_matches) {
    for (const auto& ci : s->case_items) {
      if (ci.is_default) continue;
      for (const auto* pat : ci.patterns) {
        CheckMatchesPattern(pat, diag);
        WalkExprForMatchesOp(pat, diag);
      }
    }
  }
  if (s->condition) WalkExprForMatchesOp(s->condition, diag);
  if (s->expr) WalkExprForMatchesOp(s->expr, diag);
  if (s->lhs) WalkExprForMatchesOp(s->lhs, diag);
  if (s->rhs) WalkExprForMatchesOp(s->rhs, diag);
  if (s->for_cond) WalkExprForMatchesOp(s->for_cond, diag);
  for (auto* sub : s->stmts) WalkStmtForMatchesPattern(sub, diag);
  for (auto* sub : s->fork_stmts) WalkStmtForMatchesPattern(sub, diag);
  WalkStmtForMatchesPattern(s->then_branch, diag);
  WalkStmtForMatchesPattern(s->else_branch, diag);
  WalkStmtForMatchesPattern(s->body, diag);
  WalkStmtForMatchesPattern(s->for_body, diag);
  for (auto& ci : s->case_items) WalkStmtForMatchesPattern(ci.body, diag);
  for (auto& ri : s->randcase_items)
    WalkStmtForMatchesPattern(ri.second, diag);
}

void Elaborator::ValidateMatchesPatternIntegral(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body) WalkStmtForMatchesPattern(item->body, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        WalkStmtForMatchesPattern(s, diag_);
    }
  }
}

// §12.6.1: a pattern-matching case statement compares its tested expression
// against the patterns of each item, so the tested expression and the patterns
// must share a known type. A real-valued selector cannot have the same type as
// an integral constant pattern, so the pairing is a static type error. Identifier
// and wildcard patterns (§12.6) match any value and impose no integral type, so
// they are left alone here.
static bool IsIntegralLiteralPattern(const Expr* pat) {
  if (!pat) return false;
  const Expr* p = pat;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    p = p->lhs;
  }
  return p && p->kind == ExprKind::kIntegerLiteral;
}

static void CheckMatchesCaseSelectorType(const Stmt* s, const TypeMap& types,
                                         DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kCase && s->case_matches && s->condition) {
    auto name = ExprIdent(s->condition);
    auto it = types.find(name);
    if (!name.empty() && it != types.end() && IsRealType(it->second)) {
      for (const auto& ci : s->case_items) {
        if (ci.is_default) continue;
        for (const auto* pat : ci.patterns) {
          if (IsIntegralLiteralPattern(pat)) {
            diag.Error(s->condition->range.start,
                       "pattern-matching case selector type differs from the "
                       "type of its integral pattern");
            break;
          }
        }
      }
    }
  }
  for (auto* sub : s->stmts) CheckMatchesCaseSelectorType(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckMatchesCaseSelectorType(sub, types, diag);
  CheckMatchesCaseSelectorType(s->then_branch, types, diag);
  CheckMatchesCaseSelectorType(s->else_branch, types, diag);
  CheckMatchesCaseSelectorType(s->body, types, diag);
  CheckMatchesCaseSelectorType(s->for_body, types, diag);
  for (const auto& ci : s->case_items)
    CheckMatchesCaseSelectorType(ci.body, types, diag);
}

void Elaborator::ValidateMatchesCaseSelectorType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body) CheckMatchesCaseSelectorType(item->body, var_types_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckMatchesCaseSelectorType(s, var_types_, diag_);
    }
  }
}

// §12.6.2: in each `e matches p` clause of an if-else predicate, e and p shall
// have the same statically known type. A real-valued left side cannot share a
// type with an integral constant pattern, so that pairing is a static type
// error. The predicate is a sequential conjunction of clauses joined by `&&&`,
// so each matches operator is reached by descending the `&&&` chain. Identifier
// and wildcard patterns impose no integral type and are left alone.
static void CheckMatchesIfPredicate(const Expr* pred, const TypeMap& types,
                                    DiagEngine& diag) {
  if (!pred || pred->kind != ExprKind::kBinary) return;
  if (pred->op == TokenKind::kAmpAmpAmp) {
    CheckMatchesIfPredicate(pred->lhs, types, diag);
    CheckMatchesIfPredicate(pred->rhs, types, diag);
    return;
  }
  if (pred->op != TokenKind::kKwMatches) return;
  auto name = ExprIdent(pred->lhs);
  auto it = types.find(name);
  if (!name.empty() && it != types.end() && IsRealType(it->second) &&
      IsIntegralLiteralPattern(pred->rhs)) {
    diag.Error(pred->range.start,
               "pattern-matching if predicate value type differs from the "
               "type of its integral pattern");
  }
}

static void CheckMatchesIfPredicateStmt(const Stmt* s, const TypeMap& types,
                                        DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kIf && s->condition) {
    CheckMatchesIfPredicate(s->condition, types, diag);
  }
  for (auto* sub : s->stmts) CheckMatchesIfPredicateStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckMatchesIfPredicateStmt(sub, types, diag);
  CheckMatchesIfPredicateStmt(s->then_branch, types, diag);
  CheckMatchesIfPredicateStmt(s->else_branch, types, diag);
  CheckMatchesIfPredicateStmt(s->body, types, diag);
  CheckMatchesIfPredicateStmt(s->for_body, types, diag);
  for (const auto& ci : s->case_items)
    CheckMatchesIfPredicateStmt(ci.body, types, diag);
}

void Elaborator::ValidateMatchesIfPredicateType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body) CheckMatchesIfPredicateStmt(item->body, var_types_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckMatchesIfPredicateStmt(s, var_types_, diag_);
    }
  }
}

void Elaborator::ValidateMixedAssignments() {
  for (const auto& [name, loc] : cont_assign_targets_) {
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc, std::format("variable '{}' has both continuous and "
                                   "procedural assignments",
                                   name));
    }
  }
  for (const auto& [name, loc] : output_port_targets_) {
    if (cont_assign_targets_.find(name) != cont_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by both output port and "
                              "continuous assignment",
                              name));
    }
    if (var_init_names_.count(name) != 0) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by output port has an "
                              "initializer",
                              name));
    }
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by output port has "
                              "procedural assignments",
                              name));
    }
  }
}

static void CheckDisableTargets(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kDisable && s->expr &&
      s->expr->kind == ExprKind::kIdentifier) {
    if (func_decls.count(s->expr->text) != 0) {
      diag.Error(s->range.start,
                 "disable statement shall not be used to disable a function");
    }
  }
  for (auto* sub : s->stmts) CheckDisableTargets(sub, func_decls, diag);
  for (auto* sub : s->fork_stmts) CheckDisableTargets(sub, func_decls, diag);
  CheckDisableTargets(s->then_branch, func_decls, diag);
  CheckDisableTargets(s->else_branch, func_decls, diag);
  CheckDisableTargets(s->body, func_decls, diag);
  CheckDisableTargets(s->for_body, func_decls, diag);
  for (auto& ci : s->case_items)
    CheckDisableTargets(ci.body, func_decls, diag);
  for (auto& ri : s->randcase_items)
    CheckDisableTargets(ri.second, func_decls, diag);
}

void Elaborator::ValidateDisableTargets(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (item->body)
        CheckDisableTargets(item->body, func_decls_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckDisableTargets(s, func_decls_, diag_);
    }
  }
}

void Elaborator::ValidateProceduralNetAssign() {
  for (const auto& [name, loc] : proc_assign_targets_) {
    if (net_names_.count(name) != 0) {
      diag_.Error(loc, std::format("net '{}' cannot be the target of a "
                                   "procedural assignment",
                                   name));
    }
  }
}

void Elaborator::ValidateDynamicArrayNba(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_dynamic) dyn_names.insert(name);
  }
  if (dyn_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body)
      CheckNbaDynamicArrayTarget(item->body, dyn_names, diag_);
    for (auto* s : item->func_body_stmts)
      CheckNbaDynamicArrayTarget(s, dyn_names, diag_);
  }
}

namespace {

bool IsArrayQueryFunc(std::string_view callee) {
  return callee == "$left" || callee == "$right" || callee == "$low" ||
         callee == "$high" || callee == "$increment" || callee == "$size" ||
         callee == "$dimensions" || callee == "$unpacked_dimensions";
}

// §20.7 treats a typedef as dynamically sized when one of its unpacked
// dimensions is a dynamic array ([], parsed as a null dimension), a queue
// ([$], a "$" identifier dimension), or a wildcard associative array ([*]).
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims) {
  for (const auto* d : dims) {
    if (d == nullptr) return true;
    if (d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*"))
      return true;
  }
  return false;
}

void CheckArrayQueryOnDynamicTypeExpr(
    const Expr* e, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!e) return;
  // A bare identifier first argument that names a dynamically sized typedef is
  // the type identifier itself, not an object of that type; querying it has no
  // defined extent.
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      !e->args.empty() && e->args[0] &&
      e->args[0]->kind == ExprKind::kIdentifier &&
      dyn_types.count(e->args[0]->text) != 0) {
    diag.Error(e->range.start,
               std::format("array query function '{}' cannot be applied "
                           "directly to dynamically sized type '{}'",
                           e->callee, e->args[0]->text));
  }
  CheckArrayQueryOnDynamicTypeExpr(e->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->true_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->false_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->base, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index_end, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->repeat_count, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->with_expr, dyn_types, diag);
  for (auto* a : e->args) CheckArrayQueryOnDynamicTypeExpr(a, dyn_types, diag);
  for (auto* el : e->elements)
    CheckArrayQueryOnDynamicTypeExpr(el, dyn_types, diag);
}

void CheckArrayQueryOnDynamicTypeStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnDynamicTypeExpr(s->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->delay, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->var_init, dyn_types, diag);
  for (auto* sub : s->stmts)
    CheckArrayQueryOnDynamicTypeStmt(sub, dyn_types, diag);
  for (auto* sub : s->fork_stmts)
    CheckArrayQueryOnDynamicTypeStmt(sub, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->then_branch, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->else_branch, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->body, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeStmt(s->for_body, dyn_types, diag);
  for (auto* init : s->for_inits)
    CheckArrayQueryOnDynamicTypeStmt(init, dyn_types, diag);
  for (auto& ci : s->case_items)
    CheckArrayQueryOnDynamicTypeStmt(ci.body, dyn_types, diag);
}

}  // namespace

void Elaborator::ValidateArrayQueryOnDynamicType(const ModuleDecl* decl) {
  // §20.7: the array query functions may not be used directly on a dynamically
  // sized type identifier. Collect such typedef names, then reject any direct
  // query on one.
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  if (dyn_types.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body)
      CheckArrayQueryOnDynamicTypeStmt(item->body, dyn_types, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnDynamicTypeStmt(s, dyn_types, diag_);
    CheckArrayQueryOnDynamicTypeExpr(item->init_expr, dyn_types, diag_);
  }
}

namespace {

// §20.14.1: the seed argument to $random shall be an integral variable. A real
// or string variable cannot hold the integral seed state, so a seed naming one
// is rejected. Other clearly integral kinds (vectors, enums, packed structs)
// are left alone to avoid false positives on legitimate seeds.
bool IsNonIntegralSeedKind(DataTypeKind k) {
  return IsRealType(k) || k == DataTypeKind::kString;
}

void CheckRandomSeedExpr(const Expr* e, const TypeMap& types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$random" &&
      !e->args.empty() && e->args[0]) {
    auto name = ExprIdent(e->args[0]);
    if (!name.empty()) {
      auto it = types.find(name);
      if (it != types.end() && IsNonIntegralSeedKind(it->second)) {
        diag.Error(e->range.start,
                   "seed argument of $random shall be an integral variable");
      }
    }
  }
  CheckRandomSeedExpr(e->lhs, types, diag);
  CheckRandomSeedExpr(e->rhs, types, diag);
  CheckRandomSeedExpr(e->condition, types, diag);
  CheckRandomSeedExpr(e->true_expr, types, diag);
  CheckRandomSeedExpr(e->false_expr, types, diag);
  CheckRandomSeedExpr(e->base, types, diag);
  CheckRandomSeedExpr(e->index, types, diag);
  CheckRandomSeedExpr(e->index_end, types, diag);
  CheckRandomSeedExpr(e->repeat_count, types, diag);
  CheckRandomSeedExpr(e->with_expr, types, diag);
  for (auto* a : e->args) CheckRandomSeedExpr(a, types, diag);
  for (auto* el : e->elements) CheckRandomSeedExpr(el, types, diag);
}

void CheckRandomSeedStmt(const Stmt* s, const TypeMap& types, DiagEngine& diag) {
  if (!s) return;
  CheckRandomSeedExpr(s->condition, types, diag);
  CheckRandomSeedExpr(s->lhs, types, diag);
  CheckRandomSeedExpr(s->rhs, types, diag);
  CheckRandomSeedExpr(s->expr, types, diag);
  CheckRandomSeedExpr(s->delay, types, diag);
  CheckRandomSeedExpr(s->var_init, types, diag);
  for (auto* sub : s->stmts) CheckRandomSeedStmt(sub, types, diag);
  for (auto* sub : s->fork_stmts) CheckRandomSeedStmt(sub, types, diag);
  CheckRandomSeedStmt(s->then_branch, types, diag);
  CheckRandomSeedStmt(s->else_branch, types, diag);
  CheckRandomSeedStmt(s->body, types, diag);
  CheckRandomSeedStmt(s->for_body, types, diag);
  for (auto* init : s->for_inits) CheckRandomSeedStmt(init, types, diag);
  for (auto& ci : s->case_items) CheckRandomSeedStmt(ci.body, types, diag);
}

}  // namespace

void Elaborator::ValidateRandomSeedType(const ModuleDecl* decl) {
  // §20.14.1: enforce that any $random seed argument naming a module variable
  // refers to an integral variable.
  for (const auto* item : decl->items) {
    if (item->body) CheckRandomSeedStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckRandomSeedStmt(s, var_types_, diag_);
    CheckRandomSeedExpr(item->init_expr, var_types_, diag_);
  }
}

namespace {

// §20.7.1: a single unpacked dimension is "variable-sized" when it is a dynamic
// array ([], stored as a null dimension), a queue ([$]), or a wildcard
// associative array ([*]) — the same classification §20.7 uses for a
// dynamically sized dimension.
bool DimIsVariableSized(const Expr* d) {
  if (d == nullptr) return true;
  return d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*");
}

using VarDimMap =
    std::unordered_map<std::string_view, const std::vector<Expr*>*>;

// §20.7.1: when a §20.7 query function is called as (v, n) on an array variable
// v with a constant dimension index n greater than 1, it is an error if the
// n-th dimension is variable-sized. The slowest-varying unpacked dimension is
// dimension 1, so unpacked_dims[n-1] names dimension n. Dimension 1 (or a query
// with no dimension argument) stays legal even when it is variable-sized, since
// a query on the outermost dynamic dimension still has a well-defined extent;
// an inner variable-sized dimension does not, because each element of the
// slower-varying dimension can hold a differently sized object. $dimensions and
// $unpacked_dimensions take no second argument, so they never reach this check.
void CheckArrayQueryOnVarDimExpr(const Expr* e, const VarDimMap& vars,
                                 DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      e->args.size() >= 2 && e->args[0] && e->args[1] &&
      e->args[0]->kind == ExprKind::kIdentifier &&
      e->args[1]->kind == ExprKind::kIntegerLiteral) {
    auto it = vars.find(e->args[0]->text);
    uint64_t n = e->args[1]->int_val;
    if (it != vars.end() && n > 1) {
      const std::vector<Expr*>& dims = *it->second;
      if (n <= dims.size() && DimIsVariableSized(dims[n - 1])) {
        diag.Error(e->range.start,
                   std::format("array query function '{}' cannot query "
                               "variable-sized dimension {} of array '{}'",
                               e->callee, n, e->args[0]->text));
      }
    }
  }
  CheckArrayQueryOnVarDimExpr(e->lhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->rhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->condition, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->true_expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->false_expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->base, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->index, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->index_end, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->repeat_count, vars, diag);
  CheckArrayQueryOnVarDimExpr(e->with_expr, vars, diag);
  for (auto* a : e->args) CheckArrayQueryOnVarDimExpr(a, vars, diag);
  for (auto* el : e->elements) CheckArrayQueryOnVarDimExpr(el, vars, diag);
}

void CheckArrayQueryOnVarDimStmt(const Stmt* s, const VarDimMap& vars,
                                 DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnVarDimExpr(s->condition, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->lhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->rhs, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->expr, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->delay, vars, diag);
  CheckArrayQueryOnVarDimExpr(s->var_init, vars, diag);
  for (auto* sub : s->stmts) CheckArrayQueryOnVarDimStmt(sub, vars, diag);
  for (auto* sub : s->fork_stmts) CheckArrayQueryOnVarDimStmt(sub, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->then_branch, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->else_branch, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->body, vars, diag);
  CheckArrayQueryOnVarDimStmt(s->for_body, vars, diag);
  for (auto* init : s->for_inits) CheckArrayQueryOnVarDimStmt(init, vars, diag);
  for (auto& ci : s->case_items)
    CheckArrayQueryOnVarDimStmt(ci.body, vars, diag);
}

}  // namespace

void Elaborator::ValidateArrayQueryOnVariableDim(const ModuleDecl* decl) {
  // Map every array variable in the module to its unpacked dimension list, then
  // reject any (v, n>1) query whose n-th dimension is variable-sized.
  VarDimMap vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->unpacked_dims.empty())
      vars.emplace(item->name, &item->unpacked_dims);
  }
  if (vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) CheckArrayQueryOnVarDimStmt(item->body, vars, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnVarDimStmt(s, vars, diag_);
    CheckArrayQueryOnVarDimExpr(item->init_expr, vars, diag_);
  }
}

namespace {

bool IsBitsCall(const Expr* e) {
  return e && e->kind == ExprKind::kSystemCall && e->callee == "$bits" &&
         e->args.size() == 1 && e->args[0];
}

// §20.6.2: a single argument that is a bare identifier names either the
// dynamically sized typedef itself (NC12) or an interface-class object (NC13);
// in either case there is no defined bit-stream size.
void CheckBitsCallExpr(
    const Expr* e, const std::unordered_set<std::string_view>& dyn_types,
    const std::unordered_set<std::string_view>& dyn_funcs,
    const std::unordered_set<std::string_view>& iface_vars, DiagEngine& diag) {
  if (!e) return;
  if (IsBitsCall(e)) {
    const Expr* a = e->args[0];
    if (a->kind == ExprKind::kIdentifier) {
      if (dyn_types.count(a->text) != 0) {
        diag.Error(e->range.start,
                   std::format("'$bits' cannot be applied directly to "
                               "dynamically sized type '{}'",
                               a->text));
      }
      if (iface_vars.count(a->text) != 0) {
        diag.Error(e->range.start,
                   std::format("'$bits' shall not be applied to interface "
                               "class object '{}'",
                               a->text));
      }
    } else if (a->kind == ExprKind::kCall) {
      std::string_view name = a->callee;
      if (name.empty() && a->lhs && a->lhs->kind == ExprKind::kIdentifier)
        name = a->lhs->text;
      if (!name.empty() && dyn_funcs.count(name) != 0) {
        diag.Error(e->range.start,
                   std::format("'$bits' shall not enclose function '{}' "
                               "whose return type is dynamically sized",
                               name));
      }
    }
  }
  CheckBitsCallExpr(e->lhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->rhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->condition, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->true_expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->false_expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->base, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->index, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->index_end, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->repeat_count, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(e->with_expr, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* a : e->args)
    CheckBitsCallExpr(a, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* el : e->elements)
    CheckBitsCallExpr(el, dyn_types, dyn_funcs, iface_vars, diag);
}

void CheckBitsCallStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_types,
    const std::unordered_set<std::string_view>& dyn_funcs,
    const std::unordered_set<std::string_view>& iface_vars, DiagEngine& diag) {
  if (!s) return;
  CheckBitsCallExpr(s->condition, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->lhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->rhs, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->expr, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->delay, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallExpr(s->var_init, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* sub : s->stmts)
    CheckBitsCallStmt(sub, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* sub : s->fork_stmts)
    CheckBitsCallStmt(sub, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->then_branch, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->else_branch, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->body, dyn_types, dyn_funcs, iface_vars, diag);
  CheckBitsCallStmt(s->for_body, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto* init : s->for_inits)
    CheckBitsCallStmt(init, dyn_types, dyn_funcs, iface_vars, diag);
  for (auto& ci : s->case_items)
    CheckBitsCallStmt(ci.body, dyn_types, dyn_funcs, iface_vars, diag);
}

}  // namespace

void Elaborator::ValidateBitsCallRestrictions(const ModuleDecl* decl) {
  // §20.6.2: $bits cannot be used directly on a dynamically sized type
  // identifier (NC12), cannot enclose a function whose return type is
  // dynamically sized (NC9), and cannot be applied to an object whose type is
  // an interface class (NC13, see §8.26).
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  std::unordered_set<std::string_view> dyn_funcs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl) continue;
    if (item->return_type.kind == DataTypeKind::kNamed &&
        dyn_types.count(item->return_type.type_name) != 0) {
      dyn_funcs.insert(item->name);
    }
  }
  std::unordered_set<std::string_view> iface_vars;
  for (const auto& [vname, cls_name] : class_var_types_) {
    const auto* cls = FindClassDecl(cls_name, unit_);
    if (cls && cls->is_interface) iface_vars.insert(vname);
  }
  if (dyn_types.empty() && dyn_funcs.empty() && iface_vars.empty()) return;

  for (const auto* item : decl->items) {
    if (item->body)
      CheckBitsCallStmt(item->body, dyn_types, dyn_funcs, iface_vars, diag_);
    for (auto* s : item->func_body_stmts)
      CheckBitsCallStmt(s, dyn_types, dyn_funcs, iface_vars, diag_);
    CheckBitsCallExpr(item->init_expr, dyn_types, dyn_funcs, iface_vars,
                      diag_);
  }
}

static bool IsConstantBitSelect(const Expr* e) {
  if (e->is_part_select_plus || e->is_part_select_minus) return false;
  if (e->index && e->index_end) return true;
  if (e->index && !e->index_end) {
    return ConstEvalInt(e->index).has_value();
  }
  return true;
}

static bool IsConstantSelect(const Expr* e) {
  if (!e) return true;
  if (e->kind == ExprKind::kIdentifier) return true;
  if (e->kind == ExprKind::kSelect) return IsConstantBitSelect(e);
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) {
      if (!IsConstantSelect(elem)) return false;
    }
    return true;
  }
  return true;
}

void Elaborator::ValidateContAssignConstSelect(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    if (!IsConstantSelect(item->assign_lhs)) {
      diag_.Error(item->loc,
                  "continuous assignment left-hand side requires a "
                  "constant select expression");
    }
  }
}

namespace {

// Reports whether an expression names any of the given run-time signals
// (module variables or nets). A part-select bound that does so cannot be a
// constant expression.
bool ExprNamesSignal(const Expr* e,
                     const std::unordered_set<std::string_view>& signals) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return signals.count(e->text) > 0;
  if (ExprNamesSignal(e->lhs, signals)) return true;
  if (ExprNamesSignal(e->rhs, signals)) return true;
  if (ExprNamesSignal(e->condition, signals)) return true;
  if (ExprNamesSignal(e->true_expr, signals)) return true;
  if (ExprNamesSignal(e->false_expr, signals)) return true;
  if (ExprNamesSignal(e->base, signals)) return true;
  if (ExprNamesSignal(e->index, signals)) return true;
  if (ExprNamesSignal(e->index_end, signals)) return true;
  if (ExprNamesSignal(e->with_expr, signals)) return true;
  if (ExprNamesSignal(e->repeat_count, signals)) return true;
  for (const auto* a : e->args)
    if (ExprNamesSignal(a, signals)) return true;
  for (const auto* el : e->elements)
    if (ExprNamesSignal(el, signals)) return true;
  return false;
}

struct PartSelectBoundsCtx {
  const std::unordered_set<std::string_view>& signals;
  // Packed vectors (no unpacked dimensions) whose declared range folds to a
  // constant, keyed by name and mapping to (left, right) bounds.
  const std::unordered_map<std::string_view, std::pair<int64_t, int64_t>>&
      ranges;
  DiagEngine& diag;
};

void CheckPartSelectBoundsExpr(const Expr* e, const PartSelectBoundsCtx& ctx) {
  if (!e) return;
  // Only a non-indexed part-select (vect[msb:lsb], not an indexed +:/-: form
  // and not a plain bit-select) on a simple packed-vector reference falls under
  // these §11.5.1 rules.
  if (e->kind == ExprKind::kSelect && e->index && e->index_end &&
      !e->is_part_select_plus && !e->is_part_select_minus && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      ctx.ranges.count(e->base->text)) {
    if (ExprNamesSignal(e->index, ctx.signals) ||
        ExprNamesSignal(e->index_end, ctx.signals)) {
      ctx.diag.Error(e->range.start,
                     "non-indexed part-select bounds shall be constant "
                     "expressions");
    } else {
      auto msb = ConstEvalInt(e->index);
      auto lsb = ConstEvalInt(e->index_end);
      if (msb && lsb) {
        const auto& range = ctx.ranges.at(e->base->text);
        bool descending = range.first >= range.second;
        // The first index shall name a more significant bit than the second.
        // For a descending declaration the more significant bit has the larger
        // index; for an ascending one it has the smaller index. Equal indices
        // (a one-bit part-select) are permitted.
        bool reversed = descending ? (*msb < *lsb) : (*msb > *lsb);
        if (reversed)
          ctx.diag.Error(e->range.start,
                         "part-select's first index must address a more "
                         "significant bit than its second index");
      }
    }
  }
  CheckPartSelectBoundsExpr(e->lhs, ctx);
  CheckPartSelectBoundsExpr(e->rhs, ctx);
  CheckPartSelectBoundsExpr(e->condition, ctx);
  CheckPartSelectBoundsExpr(e->true_expr, ctx);
  CheckPartSelectBoundsExpr(e->false_expr, ctx);
  CheckPartSelectBoundsExpr(e->base, ctx);
  CheckPartSelectBoundsExpr(e->index, ctx);
  CheckPartSelectBoundsExpr(e->index_end, ctx);
  CheckPartSelectBoundsExpr(e->with_expr, ctx);
  CheckPartSelectBoundsExpr(e->repeat_count, ctx);
  for (const auto* a : e->args) CheckPartSelectBoundsExpr(a, ctx);
  for (const auto* el : e->elements) CheckPartSelectBoundsExpr(el, ctx);
}

void CheckPartSelectBoundsStmt(const Stmt* s, const PartSelectBoundsCtx& ctx) {
  if (!s) return;
  CheckPartSelectBoundsExpr(s->lhs, ctx);
  CheckPartSelectBoundsExpr(s->rhs, ctx);
  CheckPartSelectBoundsExpr(s->expr, ctx);
  CheckPartSelectBoundsExpr(s->condition, ctx);
  for (const auto* c : s->stmts) CheckPartSelectBoundsStmt(c, ctx);
  CheckPartSelectBoundsStmt(s->then_branch, ctx);
  CheckPartSelectBoundsStmt(s->else_branch, ctx);
  CheckPartSelectBoundsStmt(s->body, ctx);
  for (const auto* fi : s->for_inits) CheckPartSelectBoundsStmt(fi, ctx);
  CheckPartSelectBoundsStmt(s->for_body, ctx);
  for (const auto* fs : s->for_steps) CheckPartSelectBoundsStmt(fs, ctx);
  CheckPartSelectBoundsExpr(s->for_cond, ctx);
  for (const auto& ci : s->case_items)
    CheckPartSelectBoundsStmt(ci.body, ctx);
  for (const auto* fs : s->fork_stmts) CheckPartSelectBoundsStmt(fs, ctx);
}

}  // namespace

void Elaborator::ValidatePartSelectBounds(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> signals;
  std::unordered_map<std::string_view, std::pair<int64_t, int64_t>> ranges;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl &&
        item->kind != ModuleItemKind::kNetDecl)
      continue;
    signals.insert(item->name);
    // Record a range only for a plain packed vector whose bounds are constant,
    // so the ordering check never fires on an unpacked array slice or on a
    // parameterized range it cannot resolve.
    if (item->unpacked_dims.empty()) {
      auto left = ConstEvalInt(item->data_type.packed_dim_left);
      auto right = ConstEvalInt(item->data_type.packed_dim_right);
      if (left && right) ranges[item->name] = {*left, *right};
    }
  }
  if (ranges.empty()) return;

  PartSelectBoundsCtx ctx{signals, ranges, diag_};
  for (const auto* item : decl->items) {
    CheckPartSelectBoundsExpr(item->assign_lhs, ctx);
    CheckPartSelectBoundsExpr(item->assign_rhs, ctx);
    CheckPartSelectBoundsExpr(item->init_expr, ctx);
    CheckPartSelectBoundsStmt(item->body, ctx);
    for (const auto* s : item->func_body_stmts)
      CheckPartSelectBoundsStmt(s, ctx);
  }
}

void Elaborator::ValidateSpecparamInParams(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    if (!item->init_expr) continue;
    for (const auto& sp : specparam_names_) {
      if (ExprContainsIdent(item->init_expr, sp)) {
        diag_.Error(item->loc,
                    std::format("parameter references specparam '{}'", sp));
        break;
      }
    }
  }
}

void Elaborator::ValidateSpecparamInDeclRange(const ModuleDecl* decl) {
  if (specparam_names_.empty()) return;

  // §6.20.5: a specify parameter is reserved for timing/delay values and may
  // not participate in the range specification of a declaration. Flag any
  // packed or unpacked dimension expression of a net or variable declaration
  // that references a specparam.
  auto check_range = [&](const Expr* range, SourceLoc loc) {
    if (!range) return;
    for (const auto& sp : specparam_names_) {
      if (ExprContainsIdent(range, sp)) {
        diag_.Error(loc,
                    std::format("specparam '{}' may not appear in a "
                                "declaration range specification",
                                sp));
        break;
      }
    }
  };

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kNetDecl &&
        item->kind != ModuleItemKind::kVarDecl)
      continue;
    check_range(item->data_type.packed_dim_left, item->loc);
    check_range(item->data_type.packed_dim_right, item->loc);
    for (const auto& [left, right] : item->data_type.extra_packed_dims) {
      check_range(left, item->loc);
      check_range(right, item->loc);
    }
    for (const auto* dim : item->unpacked_dims) {
      check_range(dim, item->loc);
    }
  }
}

static bool ExprContainsHierRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (ExprContainsHierRef(e->lhs)) return true;
  if (ExprContainsHierRef(e->rhs)) return true;
  if (ExprContainsHierRef(e->condition)) return true;
  if (ExprContainsHierRef(e->true_expr)) return true;
  if (ExprContainsHierRef(e->false_expr)) return true;
  for (auto* elem : e->elements) {
    if (ExprContainsHierRef(elem)) return true;
  }
  for (auto* arg : e->args) {
    if (ExprContainsHierRef(arg)) return true;
  }
  return false;
}

void Elaborator::ValidateValueParams(const ModuleDecl* decl,
                                     const RtlirModule* mod) {

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;

    if (item->data_type.kind == DataTypeKind::kVoid &&
        item->typedef_type.kind != DataTypeKind::kImplicit)
      continue;
    if (!item->init_expr) {
      diag_.Error(item->loc,
                  std::format("value parameter '{}' has no default value",
                              item->name));
      continue;
    }

    if (ExprContainsHierRef(item->init_expr)) {
      diag_.Error(item->loc,
                  std::format("parameter '{}' value contains a hierarchical "
                              "reference",
                              item->name));
    }

    if (item->is_localparam &&
        item->init_expr->kind == ExprKind::kAssignmentPattern &&
        !IsConstantExpr(item->init_expr, BuildParamScope(mod))) {
      diag_.Error(item->loc,
                  std::format("localparam '{}' initializer is not a constant "
                              "expression",
                              item->name));
    }
  }

  for (const auto& [pname, pval] : decl->params) {
    if (!pval) continue;
    if (ExprContainsHierRef(pval)) {
      diag_.Error(pval->range.start,
                  std::format("parameter '{}' value contains a hierarchical "
                              "reference",
                              pname));
    }
  }
}

static void CheckNoReturnInFork(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    diag.Error(s->range.start,
               "return statement is not allowed inside a fork-join block");
    return;
  }
  for (auto* sub : s->stmts) CheckNoReturnInFork(sub, diag);
  for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  CheckNoReturnInFork(s->then_branch, diag);
  CheckNoReturnInFork(s->else_branch, diag);
  CheckNoReturnInFork(s->body, diag);
  CheckNoReturnInFork(s->for_body, diag);
  for (auto& ci : s->case_items)
    CheckNoReturnInFork(ci.body, diag);
  for (auto& ri : s->randcase_items)
    CheckNoReturnInFork(ri.second, diag);
  CheckNoReturnInFork(s->assert_pass_stmt, diag);
  CheckNoReturnInFork(s->assert_fail_stmt, diag);
}

static void CheckExprForRefArgs(
    const Expr* e,
    const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier && ref_names.count(e->text)) {
    diag.Error(e->range.start,
               std::format("ref argument '{}' cannot be used inside a "
                           "fork-join_any or fork-join_none block",
                           e->text));
    return;
  }
  CheckExprForRefArgs(e->lhs, ref_names, diag);
  CheckExprForRefArgs(e->rhs, ref_names, diag);
  CheckExprForRefArgs(e->condition, ref_names, diag);
  CheckExprForRefArgs(e->true_expr, ref_names, diag);
  CheckExprForRefArgs(e->false_expr, ref_names, diag);
  CheckExprForRefArgs(e->base, ref_names, diag);
  CheckExprForRefArgs(e->index, ref_names, diag);
  CheckExprForRefArgs(e->index_end, ref_names, diag);
  CheckExprForRefArgs(e->with_expr, ref_names, diag);
  CheckExprForRefArgs(e->repeat_count, ref_names, diag);
  for (auto* arg : e->args) CheckExprForRefArgs(arg, ref_names, diag);
  for (auto* elem : e->elements) CheckExprForRefArgs(elem, ref_names, diag);
}

static void CheckStmtForRefArgs(
    const Stmt* s,
    const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!s) return;
  if (!(is_fork_block_item && s->kind == StmtKind::kVarDecl))
    CheckExprForRefArgs(s->var_init, ref_names, diag);
  CheckExprForRefArgs(s->expr, ref_names, diag);
  CheckExprForRefArgs(s->lhs, ref_names, diag);
  CheckExprForRefArgs(s->rhs, ref_names, diag);
  CheckExprForRefArgs(s->delay, ref_names, diag);
  CheckExprForRefArgs(s->cycle_delay, ref_names, diag);
  CheckExprForRefArgs(s->condition, ref_names, diag);
  CheckExprForRefArgs(s->for_cond, ref_names, diag);
  CheckExprForRefArgs(s->assert_expr, ref_names, diag);
  CheckExprForRefArgs(s->repeat_event_count, ref_names, diag);
  for (auto* dim : s->var_unpacked_dims)
    CheckExprForRefArgs(dim, ref_names, diag);
  for (auto& ev : s->events) {
    CheckExprForRefArgs(ev.signal, ref_names, diag);
    CheckExprForRefArgs(ev.iff_condition, ref_names, diag);
  }
  for (auto& ci : s->case_items)
    for (auto* p : ci.patterns) CheckExprForRefArgs(p, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckExprForRefArgs(ri.first, ref_names, diag);
  for (auto* we : s->wait_order_events)
    CheckExprForRefArgs(we, ref_names, diag);
  for (auto* sub : s->stmts)
    CheckStmtForRefArgs(sub, ref_names, false, diag);
  for (auto* sub : s->fork_stmts)
    CheckStmtForRefArgs(sub, ref_names, false, diag);
  CheckStmtForRefArgs(s->then_branch, ref_names, false, diag);
  CheckStmtForRefArgs(s->else_branch, ref_names, false, diag);
  CheckStmtForRefArgs(s->body, ref_names, false, diag);
  CheckStmtForRefArgs(s->for_body, ref_names, false, diag);
  for (auto* init : s->for_inits)
    CheckStmtForRefArgs(init, ref_names, false, diag);
  for (auto* step : s->for_steps)
    CheckStmtForRefArgs(step, ref_names, false, diag);
  for (auto& ci : s->case_items)
    CheckStmtForRefArgs(ci.body, ref_names, false, diag);
  for (auto& ri : s->randcase_items)
    CheckStmtForRefArgs(ri.second, ref_names, false, diag);
  CheckStmtForRefArgs(s->assert_pass_stmt, ref_names, false, diag);
  CheckStmtForRefArgs(s->assert_fail_stmt, ref_names, false, diag);
}

static void CheckRefArgsInForkBlocks(
    const Stmt* s,
    const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kFork &&
      (s->join_kind == TokenKind::kKwJoinAny ||
       s->join_kind == TokenKind::kKwJoinNone)) {
    for (auto* fs : s->fork_stmts) {
      bool is_block_item = (fs->kind == StmtKind::kVarDecl);
      CheckStmtForRefArgs(fs, ref_names, is_block_item, diag);
    }
  }
  for (auto* sub : s->stmts)
    CheckRefArgsInForkBlocks(sub, ref_names, diag);
  for (auto* sub : s->fork_stmts)
    CheckRefArgsInForkBlocks(sub, ref_names, diag);
  CheckRefArgsInForkBlocks(s->then_branch, ref_names, diag);
  CheckRefArgsInForkBlocks(s->else_branch, ref_names, diag);
  CheckRefArgsInForkBlocks(s->body, ref_names, diag);
  CheckRefArgsInForkBlocks(s->for_body, ref_names, diag);
  for (auto& ci : s->case_items)
    CheckRefArgsInForkBlocks(ci.body, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckRefArgsInForkBlocks(ri.second, ref_names, diag);
}

static void CheckFuncBodyStmt(
    const Stmt* s, bool is_void,
    const std::unordered_set<std::string_view>& task_names,
    std::string_view func_name, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn && s->expr && is_void) {
    diag.Error(s->range.start, "void function returns a value");
  }
  if (s->kind == StmtKind::kFork && s->join_kind != TokenKind::kKwJoinNone) {
    diag.Error(s->range.start,
               "only fork/join_none is permitted inside a function");
  }

  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kCycleDelay ||
      s->kind == StmtKind::kEventControl ||
      s->kind == StmtKind::kTimingControl || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitFork || s->kind == StmtKind::kWaitOrder ||
      s->kind == StmtKind::kExpect) {
    diag.Error(s->range.start,
               "time-controlling statement is not allowed inside a function");
  }

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall &&
      task_names.count(s->expr->callee) != 0) {
    diag.Error(s->range.start, "function cannot enable a task");
  }

  if (s->kind == StmtKind::kVarDecl && !func_name.empty() &&
      s->var_name == func_name) {
    diag.Error(s->range.start,
               std::format("declaration of '{}' conflicts with function name",
                           func_name));
  }

  if (s->kind == StmtKind::kVarDecl && s->var_is_static && s->var_init) {
    if (!IsConstantExpr(s->var_init)) {
      diag.Error(s->range.start,
                 std::format("static variable '{}' initializer must be a "
                             "constant expression",
                             s->var_name));
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS");
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }

  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;
  for (auto* sub : s->stmts)
    CheckFuncBodyStmt(sub, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->then_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->else_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->for_body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_pass_stmt, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_fail_stmt, is_void, task_names, func_name, diag);
  for (auto& ci : s->case_items)
    CheckFuncBodyStmt(ci.body, is_void, task_names, func_name, diag);
  for (auto& ri : s->randcase_items)
    CheckFuncBodyStmt(ri.second, is_void, task_names, func_name, diag);
}

// §13.3.2: an automatic task variable is deallocated when the invocation ends,
// so a reference to one must not outlive the call. Walk an expression tree
// looking for any leaf identifier naming such a variable.
static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty() &&
      auto_vars.count(e->text) != 0)
    return true;
  if (ExprRefsAutoVar(e->lhs, auto_vars)) return true;
  if (ExprRefsAutoVar(e->rhs, auto_vars)) return true;
  if (ExprRefsAutoVar(e->base, auto_vars)) return true;
  if (ExprRefsAutoVar(e->index, auto_vars)) return true;
  if (ExprRefsAutoVar(e->index_end, auto_vars)) return true;
  if (ExprRefsAutoVar(e->condition, auto_vars)) return true;
  if (ExprRefsAutoVar(e->true_expr, auto_vars)) return true;
  if (ExprRefsAutoVar(e->false_expr, auto_vars)) return true;
  if (ExprRefsAutoVar(e->with_expr, auto_vars)) return true;
  if (ExprRefsAutoVar(e->repeat_count, auto_vars)) return true;
  for (auto* a : e->args)
    if (ExprRefsAutoVar(a, auto_vars)) return true;
  for (auto* el : e->elements)
    if (ExprRefsAutoVar(el, auto_vars)) return true;
  return false;
}

// §13.3.2: the nonblocking-assignment restriction applies to a write into an
// automatic task variable's own storage, including a bit-select or part-select
// of it. A bit/part-select chain is walked down to its root name. Member access
// is deliberately not traversed: it denotes a write through a handle or
// reference whose target outlives the automatic variable.
static std::string_view NbaAutoTargetRoot(const Expr* e) {
  while (e && e->kind == ExprKind::kSelect) e = e->base;
  if (e && e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

static void CheckTaskBodyStmt(
    const Stmt* s,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn && s->expr) {
    diag.Error(s->range.start, "task returns a value");
  }

  if (s->kind == StmtKind::kNonblockingAssign && s->lhs) {
    auto target = NbaAutoTargetRoot(s->lhs);
    if (!target.empty() && auto_vars.count(target) != 0) {
      diag.Error(s->range.start,
                 "automatic task variable in nonblocking assignment");
    }
  }

  // §13.3.2: an automatic task variable shall not appear in the
  // intra-assignment event control of a nonblocking assignment, since the
  // event control can defer evaluation past the variable's lifetime.
  if (s->kind == StmtKind::kNonblockingAssign) {
    bool in_event_control = ExprRefsAutoVar(s->repeat_event_count, auto_vars);
    for (const auto& ev : s->events) {
      if (ExprRefsAutoVar(ev.signal, auto_vars) ||
          ExprRefsAutoVar(ev.iff_condition, auto_vars)) {
        in_event_control = true;
      }
    }
    if (in_event_control) {
      diag.Error(s->range.start,
                 "automatic task variable in intra-assignment event control "
                 "of nonblocking assignment");
    }
  }

  // §13.3.2: an automatic task variable shall not be traced by continuous
  // monitoring system tasks such as $monitor and $dumpvars, whose tracing
  // outlives the invocation.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kSystemCall &&
      (s->expr->callee == "$monitor" || s->expr->callee == "$dumpvars")) {
    for (auto* a : s->expr->args) {
      if (ExprRefsAutoVar(a, auto_vars)) {
        diag.Error(s->range.start,
                   "automatic task variable traced by system task");
        break;
      }
    }
  }

  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic variable in procedural continuous assignment");
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS");
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
  for (auto* sub : s->stmts) CheckTaskBodyStmt(sub, auto_vars, diag);
  for (auto* sub : s->fork_stmts) CheckTaskBodyStmt(sub, auto_vars, diag);
  CheckTaskBodyStmt(s->then_branch, auto_vars, diag);
  CheckTaskBodyStmt(s->else_branch, auto_vars, diag);
  CheckTaskBodyStmt(s->body, auto_vars, diag);
  CheckTaskBodyStmt(s->for_body, auto_vars, diag);
  for (auto& ci : s->case_items)
    CheckTaskBodyStmt(ci.body, auto_vars, diag);
}

static void CollectAutoVarNames(const Stmt* s, bool task_is_auto,
                                std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {

    if (task_is_auto && !s->var_is_static) {
      out.insert(s->var_name);
    } else if (!task_is_auto && s->var_is_automatic) {
      out.insert(s->var_name);
    }
  }
  for (auto* sub : s->stmts) CollectAutoVarNames(sub, task_is_auto, out);
  CollectAutoVarNames(s->then_branch, task_is_auto, out);
  CollectAutoVarNames(s->else_branch, task_is_auto, out);
  CollectAutoVarNames(s->body, task_is_auto, out);
  CollectAutoVarNames(s->for_body, task_is_auto, out);
  for (auto& ci : s->case_items)
    CollectAutoVarNames(ci.body, task_is_auto, out);
}

void Elaborator::ValidateFunctionBody(const ModuleItem* item) {

  ValidateRefLifetime(item, diag_);

  ValidateConstRefWriteProtection(item, diag_);

  for (const auto& arg : item->func_args) {
    if (arg.data_type.kind == DataTypeKind::kNamed &&
        arg.data_type.type_name == "weak_reference" &&
        !arg.data_type.type_params.empty()) {
      const auto& tp = arg.data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed || !class_names_.count(tp.type_name)) {
        diag_.Error(item->loc,
                    "weak_reference type parameter shall be a class type");
      }
    }
    if (arg.default_value && !item->is_ansi_ports) {
      diag_.Error(item->loc,
                  std::format("default argument values are only allowed with "
                              "ANSI-style port declarations for '{}'",
                              arg.name));
    }
  }

  {
    std::unordered_set<std::string_view> ref_names;
    for (const auto& arg : item->func_args) {
      if (arg.direction == Direction::kRef && !arg.is_ref_static) {
        ref_names.insert(arg.name);
      }
    }
    if (!ref_names.empty()) {
      for (auto* s : item->func_body_stmts)
        CheckRefArgsInForkBlocks(s, ref_names, diag_);
    }
  }

  if (item->kind == ModuleItemKind::kTaskDecl) {
    bool is_auto = item->is_automatic;

    std::unordered_set<std::string_view> auto_vars;
    if (is_auto) {
      for (const auto& arg : item->func_args) {
        auto_vars.insert(arg.name);
      }
    }
    for (auto* s : item->func_body_stmts) {
      CollectAutoVarNames(s, is_auto, auto_vars);
    }
    for (auto* s : item->func_body_stmts) {
      CheckTaskBodyStmt(s, auto_vars, diag_);
    }
    return;
  }
  if (item->kind != ModuleItemKind::kFunctionDecl) return;
  bool is_void = (item->return_type.kind == DataTypeKind::kVoid);
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, is_void, task_names_, item->name, diag_);
  }
}

namespace {

void CollectIdentLeaves(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!e->text.empty() && e->text.front() != '$') out.push_back(e);
      return;
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      for (auto* a : e->args) CollectIdentLeaves(a, out);
      return;
    case ExprKind::kMemberAccess:
      CollectIdentLeaves(e->lhs, out);
      return;
    case ExprKind::kTypeRef:
      return;
    default:
      break;
  }
  CollectIdentLeaves(e->lhs, out);
  CollectIdentLeaves(e->rhs, out);
  CollectIdentLeaves(e->base, out);
  CollectIdentLeaves(e->index, out);
  CollectIdentLeaves(e->index_end, out);
  CollectIdentLeaves(e->condition, out);
  CollectIdentLeaves(e->true_expr, out);
  CollectIdentLeaves(e->false_expr, out);
  CollectIdentLeaves(e->repeat_count, out);
  CollectIdentLeaves(e->with_expr, out);
  for (auto* a : e->args) CollectIdentLeaves(a, out);
  for (auto* el : e->elements) CollectIdentLeaves(el, out);
}

}

void Elaborator::ValidateFunctionArgDefaultsScope(const ModuleItem* item) {
  if (!item) return;
  if (!item->is_ansi_ports) return;
  if (!item->method_class.empty()) return;
  std::unordered_set<std::string_view> prior_args;
  for (const auto& arg : item->func_args) {
    if (arg.default_value) {
      std::vector<const Expr*> idents;
      CollectIdentLeaves(arg.default_value, idents);
      for (const auto* e : idents) {
        auto name = e->text;
        if (name.empty()) continue;
        if (prior_args.count(name)) continue;
        if (declared_names_.count(name)) continue;
        if (ansi_port_names_.count(name)) continue;
        if (non_ansi_complete_ports_.count(name)) continue;
        if (non_ansi_partial_ports_.count(name)) continue;
        if (const_names_.count(name)) continue;
        if (enum_member_names_.count(name)) continue;
        if (specparam_names_.count(name)) continue;
        if (class_names_.count(name)) continue;
        if (class_var_names_.count(name)) continue;
        if (task_names_.count(name)) continue;
        if (func_decls_.count(name)) continue;
        if (interface_inst_types_.count(name)) continue;
        if (checker_inst_names_.count(name)) continue;
        diag_.Error(e->range.start,
                    std::format("default value for '{}' references '{}' "
                                "which is not declared in the subroutine's "
                                "declaring scope",
                                arg.name, name));
      }
    }
    if (!arg.name.empty()) prior_args.insert(arg.name);
  }
}

static void CheckAutoVarWritesInProc(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kIdentifier &&
      auto_vars.count(s->lhs->text) != 0) {
    diag.Error(s->range.start,
               "automatic variable in nonblocking assignment");
  }
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic variable in procedural continuous assignment");
    }
  }
  for (auto* sub : s->stmts) CheckAutoVarWritesInProc(sub, auto_vars, diag);
  for (auto* sub : s->fork_stmts)
    CheckAutoVarWritesInProc(sub, auto_vars, diag);
  CheckAutoVarWritesInProc(s->then_branch, auto_vars, diag);
  CheckAutoVarWritesInProc(s->else_branch, auto_vars, diag);
  CheckAutoVarWritesInProc(s->body, auto_vars, diag);
  CheckAutoVarWritesInProc(s->for_body, auto_vars, diag);
  for (auto& ci : s->case_items)
    CheckAutoVarWritesInProc(ci.body, auto_vars, diag);
}

void Elaborator::ValidateAutomaticVarProcWrites(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock;
    if (!is_proc || !item->body) continue;
    std::unordered_set<std::string_view> auto_vars;
    CollectAutoVarNames(item->body, false, auto_vars);
    if (auto_vars.empty()) continue;
    CheckAutoVarWritesInProc(item->body, auto_vars, diag_);
  }
}

namespace {

// Walks one statement subtree enforcing §12.8 rules for break, continue, and
// return. `loop_depth` counts loops reachable from this point without
// crossing a fork-join boundary; `fork_depth` counts enclosing fork-joins.
// `in_subroutine` is true when the walk originated in a function or task body.
void CheckJumpRules(const Stmt* s, int loop_depth, int fork_depth,
                    bool in_subroutine, DiagEngine& diag) {
  if (!s) return;

  switch (s->kind) {
    case StmtKind::kBreak:
      if (loop_depth == 0) {
        if (fork_depth > 0) {
          diag.Error(s->range.start,
                     "break inside fork-join cannot exit a loop outside the "
                     "fork-join block");
        } else {
          diag.Error(s->range.start, "break statement is not inside a loop");
        }
      }
      return;
    case StmtKind::kContinue:
      if (loop_depth == 0) {
        if (fork_depth > 0) {
          diag.Error(s->range.start,
                     "continue inside fork-join cannot affect a loop outside "
                     "the fork-join block");
        } else {
          diag.Error(s->range.start,
                     "continue statement is not inside a loop");
        }
      }
      return;
    case StmtKind::kReturn:
      if (!in_subroutine) {
        diag.Error(s->range.start,
                   "return statement is only allowed inside a subroutine");
      }
      return;
    default:
      break;
  }

  if (s->kind == StmtKind::kFor || s->kind == StmtKind::kForeach ||
      s->kind == StmtKind::kWhile || s->kind == StmtKind::kForever ||
      s->kind == StmtKind::kRepeat || s->kind == StmtKind::kDoWhile) {
    int next_loop = loop_depth + 1;
    CheckJumpRules(s->body, next_loop, fork_depth, in_subroutine, diag);
    CheckJumpRules(s->for_body, next_loop, fork_depth, in_subroutine, diag);
    for (auto* init : s->for_inits)
      CheckJumpRules(init, loop_depth, fork_depth, in_subroutine, diag);
    for (auto* step : s->for_steps)
      CheckJumpRules(step, loop_depth, fork_depth, in_subroutine, diag);
    return;
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts)
      CheckJumpRules(sub, 0, fork_depth + 1, in_subroutine, diag);
    return;
  }

  for (auto* sub : s->stmts)
    CheckJumpRules(sub, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->then_branch, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->else_branch, loop_depth, fork_depth, in_subroutine, diag);
  for (auto& ci : s->case_items)
    CheckJumpRules(ci.body, loop_depth, fork_depth, in_subroutine, diag);
  for (auto& ri : s->randcase_items)
    CheckJumpRules(ri.second, loop_depth, fork_depth, in_subroutine, diag);
  CheckJumpRules(s->assert_pass_stmt, loop_depth, fork_depth, in_subroutine,
                 diag);
  CheckJumpRules(s->assert_fail_stmt, loop_depth, fork_depth, in_subroutine,
                 diag);
}

// Map literal expression kinds whose type is obvious from the syntax alone
// to the corresponding DataTypeKind. Returns kImplicit when no narrow
// classification is possible without full expression type inference.
DataTypeKind ObviousLiteralKind(const Expr* e) {
  if (!e) return DataTypeKind::kImplicit;
  switch (e->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kString;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kTimeLiteral:
      return DataTypeKind::kTime;
    default:
      return DataTypeKind::kImplicit;
  }
}

// In a value-returning function, a return statement shall carry an
// expression of the correct type. The void-with-expression case is
// reported elsewhere; the type check here catches narrow but clearly
// wrong mismatches (string-vs-integral, real-vs-string, etc.).
void CheckValueReturningFuncReturn(const Stmt* s, std::string_view func_name,
                                   const DataType& return_type,
                                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    if (s->expr == nullptr) {
      diag.Error(s->range.start,
                 std::format("return statement in non-void function '{}' "
                             "shall have an expression",
                             func_name));
      return;
    }
    DataTypeKind expr_kind = ObviousLiteralKind(s->expr);
    if (expr_kind != DataTypeKind::kImplicit) {
      DataType expr_type;
      expr_type.kind = expr_kind;
      if (!IsAssignmentCompatible(return_type, expr_type)) {
        diag.Error(s->range.start,
                   std::format("return expression in function '{}' is not "
                               "assignment-compatible with the function's "
                               "return type",
                               func_name));
      }
    }
    return;
  }
  for (auto* sub : s->stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  for (auto* sub : s->fork_stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->then_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->else_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->body, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->for_body, func_name, return_type, diag);
  for (auto& ci : s->case_items)
    CheckValueReturningFuncReturn(ci.body, func_name, return_type, diag);
  for (auto& ri : s->randcase_items)
    CheckValueReturningFuncReturn(ri.second, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->assert_pass_stmt, func_name, return_type,
                                diag);
  CheckValueReturningFuncReturn(s->assert_fail_stmt, func_name, return_type,
                                diag);
}

// §12.7.3 — the leftmost identifier reached by descending an lvalue through
// index selects, member accesses, and increment/decrement operators. Names
// the object an assignment ultimately writes.
static std::string_view LvalueRootName(const Expr* e) {
  while (e) {
    switch (e->kind) {
      case ExprKind::kIdentifier:
        return e->text;
      case ExprKind::kSelect:
        e = e->base;
        break;
      case ExprKind::kMemberAccess:
        e = e->lhs;
        break;
      case ExprKind::kUnary:
      case ExprKind::kPostfixUnary:
        e = e->lhs ? e->lhs : e->base;
        break;
      default:
        return {};
    }
  }
  return {};
}

// §12.7.3 — the identifier naming the array a foreach iterates over. For a
// hierarchical designator (a.b.arr) this is the trailing member name.
static std::string_view ForeachArrayName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return e->text;
  return {};
}

static bool IsIncDecExpr(const Expr* e) {
  if (!e) return false;
  if (e->kind != ExprKind::kUnary && e->kind != ExprKind::kPostfixUnary)
    return false;
  return e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus;
}

// §12.7.3 — foreach loop variables are read-only. Reports every statement in
// the loop body that assigns to (or increments/decrements) one of `vars`.
static void CheckForeachVarsReadOnly(
    const Stmt* s, const std::unordered_set<std::string_view>& vars,
    DiagEngine& diag) {
  if (!s) return;
  const Expr* target = nullptr;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      target = s->lhs;
      break;
    case StmtKind::kExprStmt:
      if (IsIncDecExpr(s->expr)) target = s->expr;
      break;
    default:
      break;
  }
  if (target) {
    auto root = LvalueRootName(target);
    if (!root.empty() && vars.count(root)) {
      diag.Error(s->range.start,
                 std::format("foreach loop variable '{}' is read-only and "
                             "cannot be assigned",
                             root));
    }
  }
  for (auto* sub : s->stmts) CheckForeachVarsReadOnly(sub, vars, diag);
  CheckForeachVarsReadOnly(s->then_branch, vars, diag);
  CheckForeachVarsReadOnly(s->else_branch, vars, diag);
  CheckForeachVarsReadOnly(s->body, vars, diag);
  CheckForeachVarsReadOnly(s->for_body, vars, diag);
  for (auto* sub : s->for_inits) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto* sub : s->for_steps) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto* sub : s->fork_stmts) CheckForeachVarsReadOnly(sub, vars, diag);
  for (auto& ci : s->case_items)
    CheckForeachVarsReadOnly(ci.body, vars, diag);
}

static bool IsIntegralVectorKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §12.7.3 — the number of dimensions a foreach can address on an
// integral/vector array declaration: its packed dimensions plus its unpacked
// dimensions, all of which are visible directly on the declaration.
static int ForeachDimCount(const ModuleItem* decl) {
  int packed = (decl->data_type.packed_dim_left != nullptr ? 1 : 0) +
               static_cast<int>(decl->data_type.extra_packed_dims.size());
  int unpacked = static_cast<int>(decl->unpacked_dims.size());
  return packed + unpacked;
}

// §12.7.3 — applies the foreach-loop semantic rules to every foreach statement
// reachable from `s`.
static void CheckForeachInStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& arrays,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForeach) {
    std::string_view arr_name = ForeachArrayName(s->expr);

    std::unordered_set<std::string_view> named_vars;
    for (auto v : s->foreach_vars) {
      if (v.empty()) continue;
      named_vars.insert(v);
      // A loop variable shall not reuse the array's identifier.
      if (!arr_name.empty() && v == arr_name) {
        diag.Error(s->range.start,
                   std::format("foreach loop variable '{}' may not have the "
                               "same name as the array it iterates over",
                               v));
      }
    }

    if (!named_vars.empty())
      CheckForeachVarsReadOnly(s->body, named_vars, diag);

    // The loop-variable count may not exceed the array's dimensionality. Only
    // checked for module-level integral/vector arrays whose dimension count is
    // fully determined by the declaration (typedef'd or aggregate types may
    // contribute hidden packed dimensions, so they are left alone).
    auto it = arrays.find(arr_name);
    if (it != arrays.end() &&
        IsIntegralVectorKind(it->second->data_type.kind)) {
      int dims = ForeachDimCount(it->second);
      if (static_cast<int>(s->foreach_vars.size()) > dims) {
        diag.Error(
            s->range.start,
            std::format("foreach lists {} loop variables but array '{}' has "
                        "only {} dimension(s)",
                        s->foreach_vars.size(), arr_name, dims));
      }
    }
  }
  for (auto* sub : s->stmts) CheckForeachInStmt(sub, arrays, diag);
  CheckForeachInStmt(s->then_branch, arrays, diag);
  CheckForeachInStmt(s->else_branch, arrays, diag);
  CheckForeachInStmt(s->body, arrays, diag);
  CheckForeachInStmt(s->for_body, arrays, diag);
  for (auto* sub : s->for_inits) CheckForeachInStmt(sub, arrays, diag);
  for (auto* sub : s->for_steps) CheckForeachInStmt(sub, arrays, diag);
  for (auto* sub : s->fork_stmts) CheckForeachInStmt(sub, arrays, diag);
  for (auto& ci : s->case_items) CheckForeachInStmt(ci.body, arrays, diag);
}

}  // namespace

void Elaborator::ValidateForeachLoops(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> arrays;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      arrays.emplace(item->name, item);
  }
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock;
    if (is_proc && item->body) {
      CheckForeachInStmt(item->body, arrays, diag_);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts)
        CheckForeachInStmt(s, arrays, diag_);
    }
  }
}

void Elaborator::ValidateJumpStatements(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock;
    if (is_proc && item->body) {
      CheckJumpRules(item->body, 0, 0, /*in_subroutine=*/false, diag_);
      continue;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      bool is_value_returning = false;
      if (item->kind == ModuleItemKind::kFunctionDecl) {
        is_value_returning = (item->return_type.kind != DataTypeKind::kVoid);
      }
      for (auto* s : item->func_body_stmts) {
        CheckJumpRules(s, 0, 0, /*in_subroutine=*/true, diag_);
        if (is_value_returning) {
          CheckValueReturningFuncReturn(s, item->name, item->return_type,
                                        diag_);
        }
      }
    }
  }
}

static bool BodyContainsFork(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kFork) return true;
  for (auto* sub : s->stmts)
    if (BodyContainsFork(sub)) return true;
  if (BodyContainsFork(s->then_branch)) return true;
  if (BodyContainsFork(s->else_branch)) return true;
  if (BodyContainsFork(s->body)) return true;
  if (BodyContainsFork(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsFork(ci.body)) return true;
  return false;
}

static bool BodyContainsNonblocking(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kNonblockingAssign) return true;
  for (auto* sub : s->stmts)
    if (BodyContainsNonblocking(sub)) return true;
  if (BodyContainsNonblocking(s->then_branch)) return true;
  if (BodyContainsNonblocking(s->else_branch)) return true;
  if (BodyContainsNonblocking(s->body)) return true;
  if (BodyContainsNonblocking(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsNonblocking(ci.body)) return true;
  return false;
}

// §13.4.3 (c): a constant function may not contain anything that schedules
// an event to fire after the function has returned — that covers every
// timing-control / waiting / event-trigger statement, not just nonblocking
// assignments.
static bool BodyContainsEventScheduling(const Stmt* s) {
  if (!s) return false;
  switch (s->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kEventControl:
    case StmtKind::kTimingControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
    case StmtKind::kWaitOrder:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kExpect:
      return true;
    default:
      break;
  }
  for (auto* sub : s->stmts)
    if (BodyContainsEventScheduling(sub)) return true;
  if (BodyContainsEventScheduling(s->then_branch)) return true;
  if (BodyContainsEventScheduling(s->else_branch)) return true;
  if (BodyContainsEventScheduling(s->body)) return true;
  if (BodyContainsEventScheduling(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (BodyContainsEventScheduling(ci.body)) return true;
  return false;
}

static void CollectLocalDeclNames(const Stmt* s,
                                  std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) {
    if (!s->var_name.empty()) out.insert(s->var_name);
  }
  for (auto* sub : s->stmts) CollectLocalDeclNames(sub, out);
  CollectLocalDeclNames(s->then_branch, out);
  CollectLocalDeclNames(s->else_branch, out);
  CollectLocalDeclNames(s->body, out);
  CollectLocalDeclNames(s->for_body, out);
  for (auto* init : s->for_inits) CollectLocalDeclNames(init, out);
  for (auto& ci : s->case_items) CollectLocalDeclNames(ci.body, out);
  for (auto* fs : s->fork_stmts) CollectLocalDeclNames(fs, out);
}

// §13.4.3 (e) — true when the expr is a `.`-separated path that reaches
// outside the function's own scope (any kMemberAccess whose leftmost LHS is
// not a name the function declared, that isn't a built-in method call).
static const Expr* LeftmostIdentifier(const Expr* e) {
  while (e && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e;
}

static bool IsBuiltinMethodOnLocal(
    const Expr* call,
    const std::unordered_set<std::string_view>& local_names) {
  if (!call || call->kind != ExprKind::kCall) return false;
  if (!call->lhs || call->lhs->kind != ExprKind::kMemberAccess) return false;
  const Expr* root = LeftmostIdentifier(call->lhs);
  if (!root || root->kind != ExprKind::kIdentifier) return false;
  return local_names.count(root->text) > 0;
}

struct ConstFuncBodyCheck {
  std::string_view func_name;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& local_names;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_decls;
  std::unordered_set<std::string_view>* visited;
  DiagEngine& diag;
  SourceLoc loc;
  bool failed = false;
};

static bool ValidateConstantFunction(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names,
    const std::unordered_set<std::string_view>& function_names,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_decls,
    std::unordered_set<std::string_view>* visited, DiagEngine& diag);

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk);

static void WalkConstFuncExprChildren(const Expr* e,
                                      ConstFuncBodyCheck& chk) {
  WalkConstFuncExpr(e->lhs, chk);
  WalkConstFuncExpr(e->rhs, chk);
  WalkConstFuncExpr(e->condition, chk);
  WalkConstFuncExpr(e->true_expr, chk);
  WalkConstFuncExpr(e->false_expr, chk);
  WalkConstFuncExpr(e->base, chk);
  WalkConstFuncExpr(e->index, chk);
  WalkConstFuncExpr(e->index_end, chk);
  WalkConstFuncExpr(e->repeat_count, chk);
  for (auto* a : e->args) WalkConstFuncExpr(a, chk);
  for (auto* el : e->elements) WalkConstFuncExpr(el, chk);
}

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk) {
  if (!e || chk.failed) return;
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      // §13.4.3 (h)
      if (e->text == chk.func_name) return;
      if (chk.local_names.count(e->text)) return;
      if (chk.param_names.count(e->text)) return;
      if (chk.function_names.count(e->text)) return;
      chk.diag.Error(
          chk.loc,
          std::format(
              "constant function '{}' references identifier '{}' that is not "
              "a parameter, function name, or local declaration",
              chk.func_name, e->text));
      chk.failed = true;
      return;
    }
    case ExprKind::kMemberAccess: {
      // §13.4.3 (e) — `.` paths from a non-local root mean a hierarchical
      // reach outside the function.
      const Expr* root = LeftmostIdentifier(e);
      if (root && root->kind == ExprKind::kIdentifier &&
          !chk.local_names.count(root->text) &&
          !chk.param_names.count(root->text)) {
        chk.diag.Error(
            chk.loc,
            std::format(
                "constant function '{}' shall not contain hierarchical "
                "references",
                chk.func_name));
        chk.failed = true;
        return;
      }
      WalkConstFuncExprChildren(e, chk);
      return;
    }
    case ExprKind::kSystemCall: {
      // §13.4.3 (g) — only the §11.2.1 constant-system-function whitelist is
      // legal inside a constant function body. The single carve-out is the
      // elaboration severity tasks (§20.10.1), which are statements, not
      // expressions, so they are handled when the simulator evaluates the
      // function body.
      if (!IsConstantSysFunc(e->callee)) {
        chk.diag.Error(
            chk.loc,
            std::format(
                "constant function '{}' calls non-constant system function "
                "'{}'",
                chk.func_name, e->callee));
        chk.failed = true;
        return;
      }
      WalkConstFuncExprChildren(e, chk);
      return;
    }
    case ExprKind::kCall: {
      // §13.4.3 (f) — built-in methods invoked on a local variable are the
      // explicit exception in the LRM; otherwise the callee must be a known
      // function so that the recursive constant-function check applies.
      if (IsBuiltinMethodOnLocal(e, chk.local_names)) {
        for (auto* a : e->args) WalkConstFuncExpr(a, chk);
        return;
      }
      if (!e->callee.empty() && !chk.function_names.count(e->callee) &&
          e->callee != chk.func_name) {
        chk.diag.Error(
            chk.loc,
            std::format(
                "constant function '{}' invokes '{}' which is not a constant "
                "function",
                chk.func_name, e->callee));
        chk.failed = true;
        return;
      }
      // §13.4.3 (f) — the nested callee must itself satisfy the
      // constant-function constraints. Recurse into its body, guarding
      // against direct or mutual recursion by tracking visited names.
      if (!e->callee.empty() && chk.func_decls && chk.visited &&
          e->callee != chk.func_name &&
          !chk.visited->count(e->callee)) {
        auto it = chk.func_decls->find(e->callee);
        if (it != chk.func_decls->end()) {
          if (!ValidateConstantFunction(it->second, chk.loc, chk.param_names,
                                        chk.function_names, chk.func_decls,
                                        chk.visited, chk.diag)) {
            chk.failed = true;
            return;
          }
        }
      }
      WalkConstFuncExprChildren(e, chk);
      return;
    }
    default:
      WalkConstFuncExprChildren(e, chk);
      return;
  }
}

static void WalkConstFuncStmt(const Stmt* s, ConstFuncBodyCheck& chk) {
  if (!s || chk.failed) return;
  WalkConstFuncExpr(s->condition, chk);
  WalkConstFuncExpr(s->lhs, chk);
  WalkConstFuncExpr(s->rhs, chk);
  // §13.4.3: system task calls within a constant function are ignored at
  // evaluation time rather than rejected at validation time. A bare
  // statement-form system call is therefore not subjected to the §11.2.1
  // sys-func whitelist; only its arguments are walked for identifier-scope
  // and hierarchical-reference checks.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kSystemCall) {
    for (auto* a : s->expr->args) WalkConstFuncExpr(a, chk);
  } else {
    WalkConstFuncExpr(s->expr, chk);
  }
  WalkConstFuncExpr(s->delay, chk);
  WalkConstFuncExpr(s->for_cond, chk);
  WalkConstFuncExpr(s->repeat_event_count, chk);
  WalkConstFuncExpr(s->assert_expr, chk);
  WalkConstFuncExpr(s->var_init, chk);
  for (auto* sub : s->stmts) WalkConstFuncStmt(sub, chk);
  WalkConstFuncStmt(s->then_branch, chk);
  WalkConstFuncStmt(s->else_branch, chk);
  WalkConstFuncStmt(s->body, chk);
  WalkConstFuncStmt(s->for_body, chk);
  for (auto* init : s->for_inits) WalkConstFuncStmt(init, chk);
  for (auto* step : s->for_steps) WalkConstFuncStmt(step, chk);
  for (auto& ci : s->case_items) {
    for (auto* pat : ci.patterns) WalkConstFuncExpr(pat, chk);
    WalkConstFuncStmt(ci.body, chk);
  }
}

static bool ValidateConstantFunction(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names,
    const std::unordered_set<std::string_view>& function_names,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_decls,
    std::unordered_set<std::string_view>* visited, DiagEngine& diag) {
  if (visited && !func->name.empty()) {
    if (!visited->insert(func->name).second) return true;
  }
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput ||
        arg.direction == Direction::kInout ||
        arg.direction == Direction::kRef) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not have {}"
                             " arguments",
                             func->name,
                             arg.direction == Direction::kOutput  ? "output"
                             : arg.direction == Direction::kInout ? "inout"
                                                                  : "ref"));
      return false;
    }
    // §13.4.3 (k) — a default argument value, if supplied, must itself be a
    // constant expression per §11.2.1.
    if (arg.default_value && !IsConstantExpr(arg.default_value)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' default value for argument '{}' is not "
              "a constant expression",
              func->name, arg.name));
      return false;
    }
  }
  for (auto* s : func->func_body_stmts) {
    if (BodyContainsFork(s)) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not contain fork",
                             func->name));
      return false;
    }
    if (BodyContainsNonblocking(s)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' shall not contain nonblocking assignments",
              func->name));
      return false;
    }
    if (BodyContainsEventScheduling(s)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' shall not contain statements that "
              "schedule events to execute after it returns",
              func->name));
      return false;
    }
  }

  std::unordered_set<std::string_view> local_names;
  for (const auto& arg : func->func_args)
    if (!arg.name.empty()) local_names.insert(arg.name);
  if (!func->name.empty()) local_names.insert(func->name);
  for (auto* s : func->func_body_stmts) CollectLocalDeclNames(s, local_names);

  ConstFuncBodyCheck chk{func->name,    param_names, function_names,
                         local_names,   func_decls,  visited,
                         diag,          loc,         /*failed=*/false};
  for (auto* s : func->func_body_stmts) WalkConstFuncStmt(s, chk);
  return !chk.failed;
}

struct ConstFuncCallCtx {
  const std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& dpi_import_names;
  DiagEngine& diag;
};

static void ValidateConstantFuncCallsInExpr(const Expr* expr, SourceLoc loc,
                                            const ConstFuncCallCtx& ctx) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    // §13.4.3 (b) — DPI imports cannot be constant functions, so any
    // attempt to invoke one in a constant context is rejected here.
    if (ctx.dpi_import_names.count(expr->callee)) {
      ctx.diag.Error(
          loc,
          std::format(
              "DPI import '{}' shall not be used as a constant function",
              expr->callee));
    } else {
      auto it = ctx.func_decls.find(expr->callee);
      if (it != ctx.func_decls.end()) {
        std::unordered_set<std::string_view> visited;
        ValidateConstantFunction(it->second, loc, ctx.param_names,
                                 ctx.function_names, &ctx.func_decls, &visited,
                                 ctx.diag);
        // §13.4.3: the arguments to a constant function call must all be
        // constant expressions per §11.2.1. The scope is empty here — the
        // call's arguments must be self-contained constants from the outer
        // (constant) context.
        ScopeMap arg_scope;
        for (auto p : ctx.param_names) arg_scope[p] = 0;
        for (auto* a : expr->args) {
          if (a && !IsConstantExpr(a, arg_scope)) {
            ctx.diag.Error(
                loc,
                std::format(
                    "constant function call '{}' has a non-constant argument",
                    expr->callee));
            break;
          }
        }
      }
    }
  }
  ValidateConstantFuncCallsInExpr(expr->lhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->rhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->condition, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->true_expr, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->false_expr, loc, ctx);
  for (auto* arg : expr->args) ValidateConstantFuncCallsInExpr(arg, loc, ctx);
  for (auto* elem : expr->elements)
    ValidateConstantFuncCallsInExpr(elem, loc, ctx);
}

static void ValidateConstFuncCallsInItems(
    const std::vector<ModuleItem*>& items, const ConstFuncCallCtx& ctx) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      ValidateConstantFuncCallsInExpr(item->init_expr, item->loc, ctx);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor) {
      if (item->gen_cond) {
        ValidateConstantFuncCallsInExpr(item->gen_cond, item->loc, ctx);
      }
      ValidateConstFuncCallsInItems(item->gen_body, ctx);
      if (item->gen_else) {
        ValidateConstFuncCallsInItems(item->gen_else->gen_body, ctx);
      }
      for (const auto& ci : item->gen_case_items) {
        ValidateConstFuncCallsInItems(ci.body, ctx);
      }
    }
  }
}

void Elaborator::ValidateConstantFunctionCalls(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> param_names;
  for (const auto& [pname, _] : decl->params) param_names.insert(pname);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl && !item->name.empty())
      param_names.insert(item->name);
  }

  std::unordered_set<std::string_view> function_names;
  for (const auto& [fname, _] : func_decls_) function_names.insert(fname);

  std::unordered_set<std::string_view> dpi_import_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kDpiImport && !item->name.empty())
      dpi_import_names.insert(item->name);
  }

  ConstFuncCallCtx ctx{func_decls_,       param_names, function_names,
                       dpi_import_names,  diag_};

  for (const auto& [name, default_expr] : decl->params) {
    if (default_expr) {
      ValidateConstantFuncCallsInExpr(default_expr, decl->range.start, ctx);
    }
  }
  ValidateConstFuncCallsInItems(decl->items, ctx);
}

// §7.7: at a DPI import call, an open-array (unsized) formal with an output
// direction may not receive a dynamic array or queue actual. The unsized
// dimension means the C side has no agreed-upon element count to write back
// into, so this association is prohibited.
void Elaborator::CheckDpiOpenArrayCall(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall || call->callee.empty()) return;
  auto it = dpi_import_decls_.find(call->callee);
  if (it == dpi_import_decls_.end() || it->second == nullptr) return;
  const ModuleItem* imp = it->second;
  // Only positional binding is analyzed; named association is left untouched.
  for (auto name : call->arg_names) {
    if (!name.empty()) return;
  }
  size_t count = std::min(call->args.size(), imp->func_args.size());
  for (size_t i = 0; i < count; ++i) {
    const FunctionArg& formal = imp->func_args[i];
    bool is_open =
        !formal.unpacked_dims.empty() && formal.unpacked_dims[0] == nullptr;
    bool is_output = formal.direction == Direction::kOutput ||
                     formal.direction == Direction::kInout;
    if (!is_open || !is_output) continue;
    const Expr* actual = call->args[i];
    if (!actual || actual->kind != ExprKind::kIdentifier) continue;
    auto vit = var_array_info_.find(actual->text);
    if (vit == var_array_info_.end()) continue;
    if (vit->second.is_dynamic || vit->second.is_queue) {
      diag_.Error(
          actual->range.start,
          std::format("a dynamic array or queue cannot be passed to the "
                      "open-array output argument of DPI import '{}'",
                      call->callee));
    }
  }
}

void Elaborator::WalkExprForDpiCalls(const Expr* e) {
  if (!e) return;
  CheckDpiOpenArrayCall(e);
  WalkExprForDpiCalls(e->lhs);
  WalkExprForDpiCalls(e->rhs);
  WalkExprForDpiCalls(e->condition);
  WalkExprForDpiCalls(e->true_expr);
  WalkExprForDpiCalls(e->false_expr);
  WalkExprForDpiCalls(e->base);
  WalkExprForDpiCalls(e->index);
  WalkExprForDpiCalls(e->index_end);
  for (auto* a : e->args) WalkExprForDpiCalls(a);
  for (auto* el : e->elements) WalkExprForDpiCalls(el);
}

void Elaborator::WalkStmtsForDpiArgs(const Stmt* s) {
  if (!s) return;
  WalkExprForDpiCalls(s->rhs);
  WalkExprForDpiCalls(s->expr);
  WalkExprForDpiCalls(s->condition);
  for (auto* sub : s->stmts) WalkStmtsForDpiArgs(sub);
  WalkStmtsForDpiArgs(s->then_branch);
  WalkStmtsForDpiArgs(s->else_branch);
  WalkStmtsForDpiArgs(s->body);
  WalkStmtsForDpiArgs(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForDpiArgs(ci.body);
}

void Elaborator::ValidateDpiOpenArrayArgs(const ModuleDecl* decl) {
  dpi_import_decls_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kDpiImport && !item->name.empty())
      dpi_import_decls_[item->name] = item;
  }
  if (dpi_import_decls_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) WalkStmtsForDpiArgs(item->body);
    for (auto* s : item->func_body_stmts) WalkStmtsForDpiArgs(s);
    WalkExprForDpiCalls(item->init_expr);
  }
}

// §13.4.4
static bool StmtSpawnsBackgroundProcess(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kNonblockingAssign) return true;
  if (s->kind == StmtKind::kEventTrigger) return true;
  if (s->kind == StmtKind::kNbEventTrigger) return true;
  if (s->kind == StmtKind::kFork &&
      s->join_kind == TokenKind::kKwJoinNone) {
    return true;
  }
  for (auto* sub : s->stmts)
    if (StmtSpawnsBackgroundProcess(sub)) return true;
  for (auto* sub : s->fork_stmts)
    if (StmtSpawnsBackgroundProcess(sub)) return true;
  if (StmtSpawnsBackgroundProcess(s->then_branch)) return true;
  if (StmtSpawnsBackgroundProcess(s->else_branch)) return true;
  if (StmtSpawnsBackgroundProcess(s->body)) return true;
  if (StmtSpawnsBackgroundProcess(s->for_body)) return true;
  if (StmtSpawnsBackgroundProcess(s->assert_pass_stmt)) return true;
  if (StmtSpawnsBackgroundProcess(s->assert_fail_stmt)) return true;
  for (auto& ci : s->case_items)
    if (StmtSpawnsBackgroundProcess(ci.body)) return true;
  for (auto& ri : s->randcase_items)
    if (StmtSpawnsBackgroundProcess(ri.second)) return true;
  return false;
}

// §13.4.4
static bool FuncSpawnsBackgroundProcess(const ModuleItem* func) {
  if (!func) return false;
  for (const auto* s : func->func_body_stmts) {
    if (StmtSpawnsBackgroundProcess(s)) return true;
  }
  return false;
}

// §13.4.4
static void CheckBackgroundFuncCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    if (it != func_decls.end() && FuncSpawnsBackgroundProcess(it->second)) {
      diag.Error(
          expr->range.start,
          std::format(
              "function '{}' schedules a background event and cannot be "
              "called from a continuous assignment",
              expr->callee));
    }
  }
  CheckBackgroundFuncCallInExpr(expr->lhs, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->rhs, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->condition, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->true_expr, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->false_expr, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->base, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->index, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->index_end, func_decls, diag);
  for (auto* arg : expr->args)
    CheckBackgroundFuncCallInExpr(arg, func_decls, diag);
  for (auto* elem : expr->elements)
    CheckBackgroundFuncCallInExpr(elem, func_decls, diag);
}

void Elaborator::ValidateBackgroundFuncCallContext(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    CheckBackgroundFuncCallInExpr(item->assign_rhs, func_decls_, diag_);
  }
}

static bool IsValidOutputArg(const Expr* e) {
  if (!e) return false;
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

static bool IsArgProvided(const Expr* expr, size_t i, std::string_view name,
                          size_t positional_count) {
  if (expr->arg_names.empty())
    return (i < expr->args.size()) && (expr->args[i] != nullptr);
  if (i < positional_count) return (expr->args[i] != nullptr);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) return true;
  }
  return false;
}

static void CheckRequiredArgs(const Expr* expr, const ModuleItem* func,
                              size_t positional_count, DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    bool provided =
        IsArgProvided(expr, i, func->func_args[i].name, positional_count);
    if (!provided && !func->func_args[i].default_value) {
      diag.Error(expr->range.start,
                 std::format("missing argument '{}' in call to '{}'",
                             func->func_args[i].name, func->name));
    }
  }
}

static void CheckNamedArgs(const Expr* expr, const ModuleItem* func,
                           DiagEngine& diag) {
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    bool found = false;
    for (size_t i = 0; i < func->func_args.size(); ++i) {
      if (func->func_args[i].name == expr->arg_names[j]) {
        found = true;
        break;
      }
    }
    if (!found) {
      diag.Error(expr->range.start,
                 std::format("no parameter '{}' in '{}'", expr->arg_names[j],
                             func->name));
    }
  }
}

static int ResolveCallArgIndex(const Expr* expr, size_t i,
                               std::string_view name, size_t positional_count) {
  if (expr->arg_names.empty()) {
    return (i < expr->args.size()) ? static_cast<int>(i) : -1;
  }
  if (i < positional_count) return static_cast<int>(i);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static void CheckOutputArgs(const Expr* expr, const ModuleItem* func,
                            size_t positional_count, DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    if (arg && !IsValidOutputArg(arg)) {
      diag.Error(arg->range.start,
                 std::format("{} argument '{}' requires a variable",
                             dir == Direction::kOutput ? "output" : "inout",
                             func->func_args[i].name));
    }
  }
}

static std::string_view RefActualNetName(
    const Expr* e, const std::unordered_set<std::string_view>& nets) {
  if (!e || nets.empty()) return {};
  if (e->kind == ExprKind::kIdentifier) {
    return nets.count(e->text) ? e->text : std::string_view{};
  }
  if (e->kind == ExprKind::kSelect) {
    return RefActualNetName(e->base, nets);
  }
  return {};
}

static void CheckRefArgsNotNets(
    const Expr* expr, const ModuleItem* func, size_t positional_count,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (net_names.empty()) return;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    if (func->func_args[i].direction != Direction::kRef) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    auto net = RefActualNetName(arg, net_names);
    if (net.empty()) continue;
    diag.Error(arg->range.start,
               std::format("net '{}' cannot be passed by reference to "
                           "argument '{}' of '{}'",
                           net, func->func_args[i].name, func->name));
  }
}

static void CheckCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  size_t param_count = func->func_args.size();
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (positional_count > param_count) {
    diag.Error(expr->range.start,
               std::format("too many arguments to '{}': expected {}, got {}",
                           func->name, param_count, positional_count));
    return;
  }
  CheckRequiredArgs(expr, func, positional_count, diag);
  CheckNamedArgs(expr, func, diag);
  CheckOutputArgs(expr, func, positional_count, diag);
  CheckRefArgsNotNets(expr, func, positional_count, net_names, diag);
}

static void CheckVoidCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    if (it != func_decls.end() &&
        it->second->kind == ModuleItemKind::kFunctionDecl &&
        it->second->return_type.kind == DataTypeKind::kVoid) {
      diag.Error(expr->range.start,
                 std::format("void function '{}' used as expression operand",
                             expr->callee));
    }
  }
  CheckVoidCallInExpr(expr->lhs, func_decls, diag);
  CheckVoidCallInExpr(expr->rhs, func_decls, diag);
  CheckVoidCallInExpr(expr->condition, func_decls, diag);
  CheckVoidCallInExpr(expr->true_expr, func_decls, diag);
  CheckVoidCallInExpr(expr->false_expr, func_decls, diag);
  for (auto* a : expr->args) CheckVoidCallInExpr(a, func_decls, diag);
  for (auto* e : expr->elements) CheckVoidCallInExpr(e, func_decls, diag);
}

static std::string_view ForbiddenFuncArgInNonProc(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty())
    return {};
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return {};
  const auto* func = it->second;
  if (func->kind != ModuleItemKind::kFunctionDecl) return {};
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput) return "output";
    if (arg.direction == Direction::kInout) return "inout";

    if (arg.direction == Direction::kRef && !arg.is_const) return "ref";
  }
  return {};
}

static void CheckNoTaskCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = decls.find(expr->callee);
    if (it != decls.end() &&
        it->second->kind == ModuleItemKind::kTaskDecl) {
      diag.Error(expr->range.start,
                 std::format("task '{}' cannot be called in an event "
                             "expression",
                             expr->callee));
    }
  }
  CheckNoTaskCallInExpr(expr->lhs, decls, diag);
  CheckNoTaskCallInExpr(expr->rhs, decls, diag);
  CheckNoTaskCallInExpr(expr->condition, decls, diag);
  CheckNoTaskCallInExpr(expr->true_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->false_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->base, decls, diag);
  CheckNoTaskCallInExpr(expr->index, decls, diag);
  CheckNoTaskCallInExpr(expr->index_end, decls, diag);
  for (auto* a : expr->args) CheckNoTaskCallInExpr(a, decls, diag);
  for (auto* e : expr->elements) CheckNoTaskCallInExpr(e, decls, diag);
}

static void CheckEventExprSingular(
    const Expr* expr,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier && !expr->text.empty()) {
    if (non_singular_vars.count(expr->text) != 0) {
      diag.Error(expr->range.start,
                 std::format("event expression references non-singular "
                             "variable '{}'; event expressions shall return "
                             "singular values",
                             expr->text));
    }
  }
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    if (non_singular_funcs.count(expr->callee) != 0) {
      diag.Error(expr->range.start,
                 std::format("event expression calls function '{}' whose "
                             "return type is non-singular; event expressions "
                             "shall return singular values",
                             expr->callee));
    }
  }
  CheckEventExprSingular(expr->lhs, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->rhs, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->condition, non_singular_vars,
                         non_singular_funcs, diag);
  CheckEventExprSingular(expr->true_expr, non_singular_vars,
                         non_singular_funcs, diag);
  CheckEventExprSingular(expr->false_expr, non_singular_vars,
                         non_singular_funcs, diag);
  for (auto* a : expr->args)
    CheckEventExprSingular(a, non_singular_vars, non_singular_funcs, diag);
  for (auto* e : expr->elements)
    CheckEventExprSingular(e, non_singular_vars, non_singular_funcs, diag);
}

static void WalkStmtForEventSingular(
    const Stmt* s,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (const auto& ev : s->events) {
      CheckEventExprSingular(ev.signal, non_singular_vars, non_singular_funcs,
                             diag);
      CheckEventExprSingular(ev.iff_condition, non_singular_vars,
                             non_singular_funcs, diag);
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtForEventSingular(sub, non_singular_vars, non_singular_funcs, diag);
  WalkStmtForEventSingular(s->then_branch, non_singular_vars,
                           non_singular_funcs, diag);
  WalkStmtForEventSingular(s->else_branch, non_singular_vars,
                           non_singular_funcs, diag);
  WalkStmtForEventSingular(s->body, non_singular_vars, non_singular_funcs,
                           diag);
  for (auto* fi : s->for_inits)
    WalkStmtForEventSingular(fi, non_singular_vars, non_singular_funcs, diag);
  WalkStmtForEventSingular(s->for_body, non_singular_vars, non_singular_funcs,
                           diag);
  for (auto* fs : s->for_steps)
    WalkStmtForEventSingular(fs, non_singular_vars, non_singular_funcs, diag);
  for (auto& ci : s->case_items)
    WalkStmtForEventSingular(ci.body, non_singular_vars, non_singular_funcs,
                             diag);
}

static void CheckCallNoOutInoutRefInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag, std::string_view context) {
  if (!expr) return;
  auto bad = ForbiddenFuncArgInNonProc(expr, func_decls);
  if (!bad.empty()) {
    diag.Error(expr->range.start,
               std::format("function '{}' has {} argument; cannot be called "
                           "in {}",
                           expr->callee, bad, context));
  }
  CheckCallNoOutInoutRefInExpr(expr->lhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->rhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->condition, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->true_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->false_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->base, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index_end, func_decls, diag, context);
  for (auto* a : expr->args)
    CheckCallNoOutInoutRefInExpr(a, func_decls, diag, context);
  for (auto* e : expr->elements)
    CheckCallNoOutInoutRefInExpr(e, func_decls, diag, context);
}

static void WalkExprForCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr) return;
  CheckCallArgs(expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->condition, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->true_expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->false_expr, func_decls, net_names, diag);
  for (auto* a : expr->args) WalkExprForCallArgs(a, func_decls, net_names, diag);
  for (auto* e : expr->elements)
    WalkExprForCallArgs(e, func_decls, net_names, diag);
}

static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!s) return;

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kIdentifier) {
    auto it = func_decls.find(s->expr->text);
    if (it != func_decls.end()) {
      const auto* func = it->second;
      bool is_task = func->kind == ModuleItemKind::kTaskDecl;
      bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                          func->return_type.kind == DataTypeKind::kVoid;
      if (!is_task && !is_void_func) {
        diag.Error(s->expr->range.start,
                   std::format("cannot omit parentheses in call to nonvoid "
                               "function '{}'",
                               s->expr->text));
      } else {
        // §13.5.5: parentheses may be omitted only when the subroutine has
        // no formal arguments, or when every formal has a default value.
        bool all_have_defaults = true;
        for (const auto& arg : func->func_args) {
          if (!arg.default_value) {
            all_have_defaults = false;
            break;
          }
        }
        if (!all_have_defaults) {
          diag.Error(s->expr->range.start,
                     std::format("cannot omit parentheses in call to '{}': "
                                 "not all formal arguments have defaults",
                                 s->expr->text));
        }
      }
    }
  }

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall) {
    for (auto* a : s->expr->args) CheckVoidCallInExpr(a, func_decls, diag);

    // §13.4.1: calling a nonvoid function as if it had no return value is
    // legal but shall issue a warning. A void'(...) cast wraps the call in a
    // kCast at the top of the expression statement and so does not reach
    // this branch, which is how the cast form suppresses the warning.
    auto fit = func_decls.find(s->expr->callee);
    if (fit != func_decls.end()) {
      const auto* func = fit->second;
      if (func->kind == ModuleItemKind::kFunctionDecl &&
          func->return_type.kind != DataTypeKind::kVoid) {
        diag.Warning(
            s->expr->range.start,
            std::format("return value of nonvoid function '{}' is discarded; "
                        "cast to void to silence this warning",
                        s->expr->callee));
      }
    }
  } else {
    CheckVoidCallInExpr(s->expr, func_decls, diag);
  }
  CheckVoidCallInExpr(s->rhs, func_decls, diag);
  CheckVoidCallInExpr(s->condition, func_decls, diag);
  CheckVoidCallInExpr(s->for_cond, func_decls, diag);

  if (s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce) {
    CheckCallNoOutInoutRefInExpr(s->rhs, func_decls, diag,
                                 "a procedural continuous assignment");
  }
  if (s->kind == StmtKind::kEventControl) {
    for (const auto& ev : s->events) {
      CheckCallNoOutInoutRefInExpr(ev.signal, func_decls, diag,
                                   "an event expression");
      CheckCallNoOutInoutRefInExpr(ev.iff_condition, func_decls, diag,
                                   "an event expression");

      CheckNoTaskCallInExpr(ev.signal, func_decls, diag);
      CheckNoTaskCallInExpr(ev.iff_condition, func_decls, diag);
    }
  }
  WalkExprForCallArgs(s->expr, func_decls, net_names, diag);
  WalkExprForCallArgs(s->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->condition, func_decls, net_names, diag);
  for (auto* sub : s->stmts)
    WalkStmtForCallArgs(sub, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->then_branch, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->else_branch, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->body, func_decls, net_names, diag);
  for (auto* fi : s->for_inits)
    WalkStmtForCallArgs(fi, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->for_body, func_decls, net_names, diag);
  for (auto* fs : s->for_steps)
    WalkStmtForCallArgs(fs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->for_cond, func_decls, net_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtForCallArgs(ci.body, func_decls, net_names, diag);
}

// A scope randomize is a randomize_call that is not a method on a class
// object — see §A.8.2's randomize_call production and its footnote 43. The
// parser leaves `randomize` as a plain identifier, so we detect the scope
// form syntactically: either a bare callee with no member-access prefix, or
// a callee reached through the `std::` package scope. The kCall's `callee`
// field carries the simple-identifier text only, so we inspect `lhs` to
// distinguish the bare and `std::` forms from a class-method `obj.randomize`.
static bool IsScopeRandomizeCall(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* lhs = expr->lhs;
  if (!lhs) return false;
  if (lhs->kind == ExprKind::kIdentifier && lhs->text == "randomize") {
    return true;
  }
  if (lhs->kind == ExprKind::kMemberAccess && lhs->rhs &&
      lhs->rhs->kind == ExprKind::kIdentifier &&
      lhs->rhs->text == "randomize" && lhs->lhs &&
      lhs->lhs->kind == ExprKind::kIdentifier && lhs->lhs->text == "std") {
    return true;
  }
  return false;
}

// Footnote 43 (§A.8.2): in a scope randomize_call, `null` is not a legal
// argument and the with-clause's parenthesized identifier_list is also
// illegal. Walks the expression tree and reports each offending site. The
// parenthesized-form check uses the `with_has_parens` AST flag set by the
// parser regardless of whether the parenthesized list happened to be empty
// or non-empty.
static void CheckScopeRandomizeRulesInExpr(const Expr* expr,
                                           DiagEngine& diag) {
  if (!expr) return;
  if (IsScopeRandomizeCall(expr)) {
    for (const auto* arg : expr->args) {
      if (arg && arg->kind == ExprKind::kIdentifier && arg->text == "null") {
        diag.Error(arg->range.start,
                   "'null' is not a legal argument to a scope randomize call");
      }
    }
    if (expr->with_has_parens) {
      diag.Error(expr->range.start,
                 "scope randomize call cannot use a parenthesized identifier "
                 "list after 'with'");
    }
  }
  CheckScopeRandomizeRulesInExpr(expr->lhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->rhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->condition, diag);
  CheckScopeRandomizeRulesInExpr(expr->true_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->false_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->base, diag);
  CheckScopeRandomizeRulesInExpr(expr->index, diag);
  CheckScopeRandomizeRulesInExpr(expr->index_end, diag);
  for (const auto* a : expr->args) CheckScopeRandomizeRulesInExpr(a, diag);
  for (const auto* e : expr->elements)
    CheckScopeRandomizeRulesInExpr(e, diag);
}

static void WalkStmtForScopeRandomize(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  CheckScopeRandomizeRulesInExpr(s->expr, diag);
  CheckScopeRandomizeRulesInExpr(s->lhs, diag);
  CheckScopeRandomizeRulesInExpr(s->rhs, diag);
  CheckScopeRandomizeRulesInExpr(s->condition, diag);
  CheckScopeRandomizeRulesInExpr(s->for_cond, diag);
  for (const auto* sub : s->stmts) WalkStmtForScopeRandomize(sub, diag);
  WalkStmtForScopeRandomize(s->then_branch, diag);
  WalkStmtForScopeRandomize(s->else_branch, diag);
  WalkStmtForScopeRandomize(s->body, diag);
  for (const auto* fi : s->for_inits) WalkStmtForScopeRandomize(fi, diag);
  WalkStmtForScopeRandomize(s->for_body, diag);
  for (const auto* fs : s->for_steps) WalkStmtForScopeRandomize(fs, diag);
  for (const auto& ci : s->case_items)
    WalkStmtForScopeRandomize(ci.body, diag);
}

void Elaborator::ValidateSubroutineCallArgs(const ModuleDecl* decl) {

  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  for (const auto* item : decl->items) {
    bool is_proc_block = item->kind == ModuleItemKind::kInitialBlock ||
                         item->kind == ModuleItemKind::kAlwaysBlock ||
                         item->kind == ModuleItemKind::kAlwaysCombBlock ||
                         item->kind == ModuleItemKind::kAlwaysFFBlock ||
                         item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                         item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc_block) WalkStmtForScopeRandomize(item->body, diag_);
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtForScopeRandomize(s, diag_);
    }
  }

  std::unordered_set<std::string_view> non_singular_vars;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    bool unpacked_array = !item->unpacked_dims.empty();
    bool unpacked_aggregate =
        (item->data_type.kind == DataTypeKind::kStruct ||
         item->data_type.kind == DataTypeKind::kUnion) &&
        !item->data_type.is_packed;
    if (unpacked_array || unpacked_aggregate)
      non_singular_vars.insert(item->name);
  }

  std::unordered_set<std::string_view> non_singular_funcs;
  auto add_if_non_singular_return = [&](const ModuleItem* item) {
    if (item->kind != ModuleItemKind::kFunctionDecl) return;
    const auto& rt = item->return_type;
    bool unpacked_aggregate =
        (rt.kind == DataTypeKind::kStruct ||
         rt.kind == DataTypeKind::kUnion) &&
        !rt.is_packed;
    if (unpacked_aggregate) non_singular_funcs.insert(item->name);
  };
  for (const auto* item : decl->items) add_if_non_singular_return(item);
  for (const auto& [name, item] : func_decls_) add_if_non_singular_return(item);
  for (const auto* item : decl->items) {
    bool is_proc_block = item->kind == ModuleItemKind::kInitialBlock ||
                         item->kind == ModuleItemKind::kAlwaysBlock ||
                         item->kind == ModuleItemKind::kAlwaysCombBlock ||
                         item->kind == ModuleItemKind::kAlwaysFFBlock ||
                         item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                         item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc_block) {
      WalkStmtForCallArgs(item->body, all_decls, net_names_, diag_);

      WalkStmtForEventSingular(item->body, non_singular_vars,
                               non_singular_funcs, diag_);

      for (const auto& ev : item->sensitivity) {
        CheckCallNoOutInoutRefInExpr(ev.signal, all_decls, diag_,
                                     "an event expression");
        CheckCallNoOutInoutRefInExpr(ev.iff_condition, all_decls, diag_,
                                     "an event expression");

        CheckNoTaskCallInExpr(ev.signal, all_decls, diag_);
        CheckNoTaskCallInExpr(ev.iff_condition, all_decls, diag_);

        CheckEventExprSingular(ev.signal, non_singular_vars,
                               non_singular_funcs, diag_);
        CheckEventExprSingular(ev.iff_condition, non_singular_vars,
                               non_singular_funcs, diag_);
      }
    }

    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        WalkStmtForCallArgs(s, all_decls, net_names_, diag_);
      }
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckVoidCallInExpr(item->assign_rhs, all_decls, diag_);

      CheckCallNoOutInoutRefInExpr(
          item->assign_rhs, all_decls, diag_,
          "a continuous assignment");
    }
  }
}

// §14.5: an expression bound to a clocking output (or inout) signal forwards to
// a module output port, so it must be a legal output-port connection — that is,
// an assignable target. Assignable forms are a simple name, a hierarchical
// reference, a bit/part-select of one, or a concatenation of such targets.
// Non-assignable forms (literals, operator expressions, calls, replications)
// cannot drive an output port and are therefore rejected. Inputs impose no such
// restriction, since any readable expression is a valid input-port connection.
static bool IsLegalClockingOutputExpr(const Expr* e) {
  if (e == nullptr) return false;
  switch (e->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kMemberAccess:
      return true;
    case ExprKind::kSelect:
      return IsLegalClockingOutputExpr(e->base);
    case ExprKind::kConcatenation: {
      if (e->elements.empty()) return false;
      for (const Expr* el : e->elements) {
        if (!IsLegalClockingOutputExpr(el)) return false;
      }
      return true;
    }
    default:
      return false;
  }
}

void Elaborator::ValidateClockingBlock(ModuleItem* item,
                                       const RtlirModule* mod) {

  if (item->name.empty() && !item->is_default_clocking) {
    diag_.Error(item->loc, "non-default clocking block must have a name");
  }

  // §14.4: a clocking skew shall be a constant expression; a parameter is an
  // acceptable form. Any skew delay that cannot be folded against the module's
  // parameter scope (e.g. a reference to a net or variable) violates the rule.
  ScopeMap skew_scope = mod ? BuildParamScope(mod) : ScopeMap{};
  auto check_skew = [&](const Expr* delay) {
    if (delay != nullptr && !IsConstantExpr(delay, skew_scope)) {
      diag_.Error(delay->range.start,
                  "clocking skew shall be a constant expression (§14.4)");
    }
  };
  check_skew(item->default_input_skew_delay);
  check_skew(item->default_output_skew_delay);
  for (const auto& sig : item->clocking_signals) {
    check_skew(sig.skew_delay);
    check_skew(sig.out_skew_delay);

    // §14.5: a hierarchical expression bound to a clocking output or inout
    // signal must be a legal output-port connection (an assignable target).
    // A clocking inout is shorthand for an input and an output sharing the
    // same signal, so it must meet the output-port rule as well — though a
    // plain variable, being assignable, remains acceptable. Input signals are
    // unconstrained here, as any readable expression is a valid input.
    if (sig.hier_expr != nullptr &&
        (sig.direction == Direction::kOutput ||
         sig.direction == Direction::kInout) &&
        !IsLegalClockingOutputExpr(sig.hier_expr)) {
      diag_.Error(
          sig.hier_expr->range.start,
          std::format("clocking {} signal '{}' is bound to an expression that "
                      "is not a legal output-port connection (§14.5)",
                      sig.direction == Direction::kInout ? "inout" : "output",
                      sig.name));
    }
  }

  if (!item->name.empty()) {
    auto& sigs = clocking_signals_[item->name];
    for (const auto& sig : item->clocking_signals) {
      sigs[sig.name] = {sig.direction};
    }
  }
}

void Elaborator::ValidateNoFormalShadowedByBodyLocal(ModuleItem* item) {
  // §16.10: a formal-argument identifier cannot be redeclared in the body of
  // the same sequence/property declaration as an assertion_variable_declaration.
  // The two name lists are harvested by the parser; the elaborator only has
  // to flag any overlap.
  if (item->prop_formals.empty() || item->prop_seq_assert_vars.empty()) {
    return;
  }
  std::unordered_set<std::string_view> formal_set(
      item->prop_formals.begin(), item->prop_formals.end());
  for (auto body_var : item->prop_seq_assert_vars) {
    if (formal_set.count(body_var) != 0) {
      diag_.Error(item->loc,
                  "local variable \"" + std::string(body_var) +
                      "\" is a formal argument and cannot be redeclared "
                      "in the body (§16.10)");
    }
  }
}

void Elaborator::ValidateRecursiveProperty(const ModuleItem* item) {
  if (item == nullptr || item->kind != ModuleItemKind::kPropertyDecl) return;

  const bool recursive = property_registry_.IsRecursiveProperty(item);

  // §16.12.17 Restriction 2 / §F.7 RESTRICTION 2: disable iff cannot be used in
  // the declaration of a recursive property. (This mirrors the rule that
  // disable iff cannot be nested.) The accept_on/reject_on family is *not*
  // affected: those operators may appear inside a recursive property.
  if (recursive && item->prop_disable_iff_count > 0) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" may not use disable iff (§16.12.17 Restriction 2)");
  }

  // §16.12.17 Restriction 1 / §F.7 RESTRICTION 1: the negation operator not and
  // the strong operators (s_nexttime, s_eventually, s_always, s_until,
  // s_until_with) cannot be applied to a property expression that instantiates
  // a property from which a recursive property is reachable.
  for (auto ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(ref);
    if (callee != nullptr &&
        property_registry_.ReachesRecursiveProperty(callee)) {
      diag_.Error(item->loc,
                  "negation or strong operator applied to property \"" +
                      std::string(ref) +
                      "\", which reaches a recursive property "
                      "(§16.12.17 Restriction 1)");
    }
  }

  // §16.12.17 Restriction 3 / §F.7 RESTRICTION 3: every recursive instance must
  // occur after a positive advance in time; a self-instantiation with no
  // intervening time advance would leave the recursion stuck at one cycle.
  if (item->prop_has_untimed_self_recursion) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" instantiates itself with no positive advance in time "
                    "(§16.12.17 Restriction 3)");
  }

  // §16.12.17 Restriction 4 / §F.7 RESTRICTION 4 applies to every recursive
  // instance regardless of whether the enclosing property is itself recursive.
  ValidateRecursivePropertyArguments(item);
}

void Elaborator::ValidateRecursivePropertyArguments(const ModuleItem* item) {
  if (item->prop_instance_args.empty()) return;

  // Formal arguments of the enclosing property p.
  std::unordered_set<std::string_view> p_formals(item->prop_formals.begin(),
                                                  item->prop_formals.end());

  for (const auto& inst : item->prop_instance_args) {
    const ModuleItem* q = property_registry_.Find(inst.callee);
    if (q == nullptr || q->kind != ModuleItemKind::kPropertyDecl) continue;
    // Restriction 4 constrains only instances of a property that participates
    // in the recursion (a recursive instance).
    if (!property_registry_.ReachesRecursiveProperty(q)) continue;

    for (std::size_t i = 0; i < inst.arg_idents.size(); ++i) {
      const auto& idents = inst.arg_idents[i];

      // (a) the actual argument expression e is itself a formal of p.
      const bool is_single_formal =
          i < inst.arg_is_single_ident.size() && inst.arg_is_single_ident[i] &&
          idents.size() == 1 && p_formals.count(idents[0]) != 0;
      if (is_single_formal) continue;

      // (b) no formal argument of p appears in e.
      bool any_p_formal = false;
      for (auto id : idents) {
        if (p_formals.count(id) != 0) {
          any_p_formal = true;
          break;
        }
      }
      if (!any_p_formal) continue;

      // (c) e is bound to a local variable formal argument of q (positional).
      const bool bound_to_local_formal =
          i < q->prop_formal_is_local.size() && q->prop_formal_is_local[i];
      if (bound_to_local_formal) continue;

      diag_.Error(item->loc,
                  "recursive instance of \"" + std::string(inst.callee) +
                      "\" passes an actual argument that contains a formal of "
                      "\"" + std::string(item->name) +
                      "\" yet is neither a formal itself nor bound to a local "
                      "variable formal (§16.12.17 Restriction 4)");
    }
  }
}

void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier) {
    auto block_it = clocking_signals_.find(e->lhs->text);
    if (block_it != clocking_signals_.end()) {

      std::string_view member;
      if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
        member = e->rhs->text;
      } else if (!e->text.empty()) {
        member = e->text;
      }
      if (!member.empty()) {
        auto sig_it = block_it->second.find(member);
        if (sig_it != block_it->second.end()) {
          if (is_lvalue && sig_it->second.direction == Direction::kInput) {
            diag_.Error(e->range.start,
                        std::format("write to input clockvar '{}.{}'",
                                    e->lhs->text, member));
          }
          if (!is_lvalue && sig_it->second.direction == Direction::kOutput) {
            diag_.Error(e->range.start,
                        std::format("read from output clockvar '{}.{}'",
                                    e->lhs->text, member));
          }
        }
      }
    }
  }

  if (!is_lvalue) {
    CheckClockvarAccessExpr(e->lhs, false);
    CheckClockvarAccessExpr(e->rhs, false);
    CheckClockvarAccessExpr(e->condition, false);
    CheckClockvarAccessExpr(e->true_expr, false);
    CheckClockvarAccessExpr(e->false_expr, false);
    for (auto* arg : e->args) CheckClockvarAccessExpr(arg, false);
    for (auto* elem : e->elements) CheckClockvarAccessExpr(elem, false);
  }
}

void Elaborator::WalkStmtsForClockvarAccess(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckClockvarAccessExpr(s->lhs, true);
    CheckClockvarAccessExpr(s->rhs, false);
  } else {
    CheckClockvarAccessExpr(s->expr, false);
    CheckClockvarAccessExpr(s->rhs, false);
  }
  for (auto* sub : s->stmts) WalkStmtsForClockvarAccess(sub);
  WalkStmtsForClockvarAccess(s->then_branch);
  WalkStmtsForClockvarAccess(s->else_branch);
  WalkStmtsForClockvarAccess(s->body);
  WalkStmtsForClockvarAccess(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForClockvarAccess(ci.body);
}

void Elaborator::ValidateClockvarAccess(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForClockvarAccess(item->body);
    }
  }
}

static bool HasCycleDelay(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kCycleDelay) return true;
  for (auto* sub : s->stmts) {
    if (HasCycleDelay(sub)) return true;
  }
  if (HasCycleDelay(s->then_branch)) return true;
  if (HasCycleDelay(s->else_branch)) return true;
  if (HasCycleDelay(s->body)) return true;
  if (HasCycleDelay(s->for_body)) return true;
  for (auto& ci : s->case_items) {
    if (HasCycleDelay(ci.body)) return true;
  }
  return false;
}

void Elaborator::ValidateCycleDelayDefaultClocking(const ModuleDecl* decl) {
  bool has_default = false;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      has_default = true;
      break;
    }
  }
  if (has_default) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body && HasCycleDelay(item->body)) {
      diag_.Error(item->loc,
                  "cycle delay (##) requires a default clocking block");
    }
  }
}

// §14.11: locate an assignment that carries a cycle-delay intra-assignment
// timing control. A synchronous drive (§14.16) reaches a clocking-block
// variable through a member access (e.g. cb.sig or vif.cb.sig), so a target
// that is a simple name can only be the illegal intra-assignment form. The walk
// returns the offending statement so its source location can be reported.
static const Stmt* FindIntraAssignCycleDelay(const Stmt* s) {
  if (!s) return nullptr;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->cycle_delay != nullptr && s->lhs != nullptr &&
      s->lhs->kind == ExprKind::kIdentifier) {
    return s;
  }
  for (auto* sub : s->stmts) {
    if (const auto* hit = FindIntraAssignCycleDelay(sub)) return hit;
  }
  if (const auto* hit = FindIntraAssignCycleDelay(s->then_branch)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->else_branch)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->body)) return hit;
  if (const auto* hit = FindIntraAssignCycleDelay(s->for_body)) return hit;
  for (auto& ci : s->case_items) {
    if (const auto* hit = FindIntraAssignCycleDelay(ci.body)) return hit;
  }
  return nullptr;
}

void Elaborator::ValidateIntraAssignCycleDelay(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      if (const Stmt* hit = FindIntraAssignCycleDelay(item->body)) {
        diag_.Error(hit->range.start,
                    "cycle delay (##) is not a legal intra-assignment delay "
                    "in a blocking or nonblocking assignment");
      }
    }
  }
}

void Elaborator::ValidateDuplicateDefaultClocking(const ModuleDecl* decl) {
  const ModuleItem* first_default = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      if (first_default) {
        diag_.Error(item->loc,
                    "only one default clocking block is allowed per scope");
        return;
      }
      first_default = item;
    }
  }
}

void Elaborator::ValidateDefaultClockingReference(const ModuleDecl* decl) {
  // §14.12: a "default clocking <id>;" assignment statement designates an
  // existing clocking block as the default. Its clocking_identifier shall be
  // the name of a clocking block. The assignment form is distinguished from
  // the inline declaration form by carrying no clocking event (the inline
  // form always declares an @(event)).
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (!item->is_default_clocking) continue;
    if (!item->clocking_event.empty()) continue;  // inline declaration form
    if (item->name.empty()) continue;
    bool names_block = false;
    for (const auto* other : decl->items) {
      if (other == item) continue;
      if (other->kind == ModuleItemKind::kClockingBlock &&
          !other->clocking_event.empty() && other->name == item->name) {
        names_block = true;
        break;
      }
    }
    if (!names_block) {
      diag_.Error(item->loc,
                  "default clocking \"" + std::string(item->name) +
                      "\" does not name a clocking block");
    }
  }
}

void Elaborator::ValidateDuplicateGlobalClocking(const ModuleDecl* decl) {
  const ModuleItem* first_global = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      if (first_global) {
        diag_.Error(item->loc,
                    "only one global clocking block is allowed per scope");
        return;
      }
      first_global = item;
    }
  }
}

namespace {

bool ExprRefsGlobalClock(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$global_clock") {
    return true;
  }
  if (ExprRefsGlobalClock(e->lhs)) return true;
  if (ExprRefsGlobalClock(e->rhs)) return true;
  if (ExprRefsGlobalClock(e->condition)) return true;
  if (ExprRefsGlobalClock(e->true_expr)) return true;
  if (ExprRefsGlobalClock(e->false_expr)) return true;
  if (ExprRefsGlobalClock(e->base)) return true;
  if (ExprRefsGlobalClock(e->index)) return true;
  if (ExprRefsGlobalClock(e->index_end)) return true;
  if (ExprRefsGlobalClock(e->repeat_count)) return true;
  if (ExprRefsGlobalClock(e->with_expr)) return true;
  for (auto* a : e->args) {
    if (ExprRefsGlobalClock(a)) return true;
  }
  for (auto* el : e->elements) {
    if (ExprRefsGlobalClock(el)) return true;
  }
  return false;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s) {
  if (!s) return nullptr;
  if (ExprRefsGlobalClock(s->expr)) return s->expr;
  if (ExprRefsGlobalClock(s->lhs)) return s->lhs;
  if (ExprRefsGlobalClock(s->rhs)) return s->rhs;
  if (ExprRefsGlobalClock(s->condition)) return s->condition;
  if (ExprRefsGlobalClock(s->assert_expr)) return s->assert_expr;
  if (ExprRefsGlobalClock(s->for_cond)) return s->for_cond;
  for (const auto& ev : s->events) {
    if (ExprRefsGlobalClock(ev.signal)) return ev.signal;
  }
  for (auto* sub : s->stmts) {
    if (auto* hit = FindGlobalClockRefInStmt(sub)) return hit;
  }
  if (auto* hit = FindGlobalClockRefInStmt(s->then_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->else_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->body)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->for_body)) return hit;
  for (auto& ci : s->case_items) {
    if (auto* hit = FindGlobalClockRefInStmt(ci.body)) return hit;
  }
  return nullptr;
}

}

void Elaborator::ValidateGlobalClockReference(const ModuleDecl* decl) {
  bool has_global = false;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      has_global = true;
      break;
    }
  }
  if (has_global) return;

  for (const auto* item : decl->items) {
    const Expr* ref = nullptr;
    if (item->body) ref = FindGlobalClockRefInStmt(item->body);
    if (!ref && ExprRefsGlobalClock(item->init_expr)) ref = item->init_expr;
    if (!ref && ExprRefsGlobalClock(item->assign_lhs)) ref = item->assign_lhs;
    if (!ref && ExprRefsGlobalClock(item->assign_rhs)) ref = item->assign_rhs;
    if (!ref && ExprRefsGlobalClock(item->prop_body_expr)) {
      ref = item->prop_body_expr;
    }
    if (!ref) {
      for (const auto& ev : item->sensitivity) {
        if (ExprRefsGlobalClock(ev.signal)) {
          ref = ev.signal;
          break;
        }
      }
    }
    if (ref) {
      diag_.Error(ref->range.start,
                  "$global_clock has no effective global clocking declaration "
                  "in any enclosing scope up to the top-level hierarchy block");
      return;
    }
  }
}

void Elaborator::ValidateContAssignToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    // §14.16.2: a continuous assignment to a variable that is associated with
    // an output (or inout) clockvar is illegal. The target may be the whole
    // variable or a bit-/part-select of it, so resolve through any selects to
    // the root identifier; a select target is rejected exactly as the whole
    // variable would be. This mirrors the root resolution the primitive and
    // procedural-continuous checks already perform for the same prohibition.
    const Expr* root = item->assign_lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
    if (root == nullptr || root->kind != ExprKind::kIdentifier) continue;
    if (IsOutputClockvarSignal(root->text)) {
      diag_.Error(item->loc,
                  std::format("continuous assignment to clocking output "
                              "variable '{}'",
                              root->text));
    }
  }
}

bool Elaborator::IsOutputClockvarSignal(std::string_view name) const {
  // §14.16.2: a clocking output/inout is implicitly tied to a same-named signal
  // in the enclosing scope (§14.3). Match the bare variable name against the
  // output/inout clockvar members collected across every clocking block.
  for (const auto& [block_name, sigs] : clocking_signals_) {
    auto it = sigs.find(name);
    if (it != sigs.end() &&
        (it->second.direction == Direction::kOutput ||
         it->second.direction == Direction::kInout)) {
      return true;
    }
  }
  return false;
}

void Elaborator::ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    const auto& terms = item->gate_terminals;
    if (terms.empty()) continue;

    auto check = [&](const Expr* t) {
      // §14.16.2: it shall be illegal to drive a variable associated with an
      // output clockvar from a primitive.
      const Expr* root = t;
      while (root != nullptr && root->kind == ExprKind::kSelect)
        root = root->base;
      if (root != nullptr && root->kind == ExprKind::kIdentifier &&
          IsOutputClockvarSignal(root->text)) {
        diag_.Error(
            root->range.start,
            std::format("primitive output drives variable '{}', which is "
                        "associated with a clocking output",
                        root->text));
      }
    };

    // For buf/not gates every terminal but the last is an output; for the
    // other driving gates the first terminal is the single output.
    if (item->gate_kind == GateKind::kBuf ||
        item->gate_kind == GateKind::kNot) {
      for (size_t i = 0; i + 1 < terms.size(); ++i) check(terms[i]);
    } else {
      check(terms[0]);
    }
  }
}

// §14.16: a synchronous drive reaches a clocking-block output (or inout)
// through a member access such as cb.sig, optionally wrapped in a bit-select
// or slice (cb.sig[2], cb.sig[8:2]). Returns true when `e` designates such a
// writable clockvar. Input clockvars are excluded here; writes to them are
// rejected separately by the clockvar-access check.
bool Elaborator::ExprTargetsWritableClockvar(const Expr* e) const {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto block_it = clocking_signals_.find(e->lhs->text);
  if (block_it == clocking_signals_.end()) return false;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier)
    member = e->rhs->text;
  else if (!e->text.empty())
    member = e->text;
  if (member.empty()) return false;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return false;
  return sig_it->second.direction == Direction::kOutput ||
         sig_it->second.direction == Direction::kInout;
}

void Elaborator::WalkStmtsForSyncDriveForm(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (ExprTargetsWritableClockvar(s->lhs)) {
      // §14.16: the only timing control permitted on a synchronous drive is a
      // leading cycle delay (## ...). A regular intra-assignment delay (# ...)
      // is not a legal form of synchronous drive to a clockvar.
      if (s->delay != nullptr) {
        diag_.Error(s->delay->range.start,
                    "intra-assignment delay (#) is not a legal synchronous "
                    "drive to a clocking output variable");
      }
    }
    // §14.16: the clockvar_expression of a synchronous drive is a bit-select,
    // slice, or whole clockvar; a concatenation target is not allowed.
    if (s->lhs != nullptr && s->lhs->kind == ExprKind::kConcatenation) {
      for (const auto* elem : s->lhs->elements) {
        if (ExprTargetsWritableClockvar(elem)) {
          diag_.Error(s->lhs->range.start,
                      "a concatenation is not a legal synchronous drive target "
                      "for a clocking output variable");
          break;
        }
      }
    }
  } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    // §14.16: writing to a clockvar by any means other than a synchronous
    // drive is an error; procedural continuous assignment (assign/force) is
    // explicitly disallowed.
    if (ExprTargetsWritableClockvar(s->lhs)) {
      diag_.Error(s->lhs->range.start,
                  "procedural continuous assignment (assign/force) to a "
                  "clocking output variable is not allowed");
    } else if (s->lhs != nullptr) {
      // §14.16.2: it is likewise illegal to write the underlying variable that
      // an output clockvar is tied to with a procedural continuous assignment.
      const Expr* root = s->lhs;
      while (root != nullptr && root->kind == ExprKind::kSelect)
        root = root->base;
      if (root != nullptr && root->kind == ExprKind::kIdentifier &&
          IsOutputClockvarSignal(root->text)) {
        diag_.Error(
            root->range.start,
            std::format("procedural continuous assignment (assign/force) to "
                        "variable '{}', which is associated with a clocking "
                        "output, is not allowed",
                        root->text));
      }
    }
  }
  for (auto* sub : s->stmts) WalkStmtsForSyncDriveForm(sub);
  WalkStmtsForSyncDriveForm(s->then_branch);
  WalkStmtsForSyncDriveForm(s->else_branch);
  WalkStmtsForSyncDriveForm(s->body);
  WalkStmtsForSyncDriveForm(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForSyncDriveForm(ci.body);
}

void Elaborator::ValidateSyncDriveForm(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) WalkStmtsForSyncDriveForm(item->body);
  }
}

static void WalkStmtsForSequenceEvents(
    Stmt* s, const std::unordered_set<std::string_view>& seq_names,
    bool in_automatic, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (auto& ev : s->events) {
      if (!ev.signal) continue;
      std::string_view name;
      bool has_args = false;
      if (ev.signal->kind == ExprKind::kIdentifier) {
        name = ev.signal->text;
      } else if (ev.signal->kind == ExprKind::kCall) {
        name = ev.signal->callee;
        has_args = !ev.signal->args.empty();
      }
      if (!name.empty() && seq_names.count(name) != 0) {
        ev.is_sequence_event = true;

        if (has_args && in_automatic) {
          diag.Error(s->range.start,
                     "sequence event arguments shall not reference "
                     "automatic variables");
        }
      }
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForSequenceEvents(sub, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->then_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->else_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->body, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->for_body, seq_names, in_automatic, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForSequenceEvents(ci.body, seq_names, in_automatic, diag);
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl) {
  if (sequence_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      if (item->body) {
        WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                   sequence_names_, false, diag_);
      }
    }

    if (item->kind == ModuleItemKind::kTaskDecl && item->body) {
      WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                 sequence_names_, item->is_automatic, diag_);
    }
  }
}

static bool IsSingleSubroutineCall(const Stmt* action) {
  if (!action) return true;
  if (action->kind == StmtKind::kNull) return true;
  if (action->kind != StmtKind::kExprStmt) return false;
  if (!action->expr) return false;
  return action->expr->kind == ExprKind::kCall ||
         action->expr->kind == ExprKind::kSystemCall;
}

static bool ContainsPostponedIllegalStmt(const Stmt* s) {
  if (!s) return false;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kCycleDelay:
      return true;
    default:
      break;
  }
  for (auto* sub : s->stmts) {
    if (ContainsPostponedIllegalStmt(sub)) return true;
  }
  if (ContainsPostponedIllegalStmt(s->then_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->else_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->body)) return true;
  if (ContainsPostponedIllegalStmt(s->for_body)) return true;
  for (const auto& ci : s->case_items) {
    if (ContainsPostponedIllegalStmt(ci.body)) return true;
  }
  return false;
}

static bool CalleeBodyHasPostponedIllegal(const ModuleItem* callee) {
  if (!callee) return false;
  if (callee->body && ContainsPostponedIllegalStmt(callee->body)) return true;
  for (auto* s : callee->func_body_stmts) {
    if (ContainsPostponedIllegalStmt(s)) return true;
  }
  return false;
}

using DeferredSubroutineMap =
    std::unordered_map<std::string_view, const ModuleItem*>;

static void CheckFinalDeferredCallee(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  if (CalleeBodyHasPostponedIllegal(it->second)) {
    diag.Warning(action->range.start,
                 std::format(
                     "§16.4: final deferred assertion calls '{}', whose body "
                     "contains statements not legally callable in the "
                     "Postponed region (§4.4.2.9)",
                     action->expr->callee));
  }
}

static void CheckDeferredCallRefArgs(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  const auto& formals = it->second->func_args;
  const auto& actuals = action->expr->args;
  size_t n = std::min(formals.size(), actuals.size());
  for (size_t i = 0; i < n; ++i) {
    if (formals[i].direction != Direction::kRef) continue;
    const Expr* a = actuals[i];
    if (!a) continue;
    if (a->kind == ExprKind::kMemberAccess) {
      diag.Error(a->range.start,
                 std::format(
                     "§16.4: cannot pass dynamic variable as actual for "
                     "ref{} formal '{}' in deferred-assertion call",
                     formals[i].is_const ? " const" : "",
                     formals[i].name));
    }
  }
}

static void CheckDeferredActionStmt(const Stmt* s,
                                    const DeferredSubroutineMap& subs,
                                    DiagEngine& diag) {
  if (!s->is_deferred) return;
  if (s->kind != StmtKind::kAssertImmediate &&
      s->kind != StmtKind::kAssumeImmediate &&
      s->kind != StmtKind::kCoverImmediate) {
    return;
  }
  if (s->assert_pass_stmt && !IsSingleSubroutineCall(s->assert_pass_stmt)) {
    diag.Warning(s->assert_pass_stmt->range.start,
                 "§16.4: deferred assertion pass action shall be a single "
                 "subroutine call");
  }
  if (s->assert_fail_stmt && !IsSingleSubroutineCall(s->assert_fail_stmt)) {
    diag.Warning(s->assert_fail_stmt->range.start,
                 "§16.4: deferred assertion fail action shall be a single "
                 "subroutine call");
  }

  if (s->is_final_deferred) {
    CheckFinalDeferredCallee(s->assert_pass_stmt, subs, diag);
    CheckFinalDeferredCallee(s->assert_fail_stmt, subs, diag);
  }

  CheckDeferredCallRefArgs(s->assert_pass_stmt, subs, diag);
  CheckDeferredCallRefArgs(s->assert_fail_stmt, subs, diag);
}

void Elaborator::WalkStmtsForDeferredActions(const Stmt* s) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForDeferredActions(sub);
  WalkStmtsForDeferredActions(s->then_branch);
  WalkStmtsForDeferredActions(s->else_branch);
  WalkStmtsForDeferredActions(s->body);
  WalkStmtsForDeferredActions(s->for_body);
  WalkStmtsForDeferredActions(s->assert_pass_stmt);
  WalkStmtsForDeferredActions(s->assert_fail_stmt);
  for (const auto& ci : s->case_items) WalkStmtsForDeferredActions(ci.body);
}

void Elaborator::ValidateDeferredAssertionActions(const ModuleDecl* decl) {

  deferred_subroutine_map_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      deferred_subroutine_map_[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {

    if (item->body) {
      WalkStmtsForDeferredActions(item->body);
    }
  }
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

}
