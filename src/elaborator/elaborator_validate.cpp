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

// §10.9.2: Type key strings that are valid in assignment patterns.
static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" ||
         key == "time" || key == "realtime" || key == "string";
}

// §5.11: Check if an assignment pattern is a replication or named form.
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

// §10.9.1: Check for duplicate index keys in a keyed array pattern.
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

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (IsArrayPatternSpecial(item->init_expr)) {
    CheckArrayPatternDuplicateIndices(item->init_expr, item->loc, diag_);
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
  // §10.9.2: Every member shall be covered by member, type, or default key.
  if (!has_default && !has_type_key) {
    CheckPatternCoverage(item, members, seen, diag);
  }
}

void Elaborator::ValidateStructInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (item->init_expr->pattern_keys.empty()) return;
  const auto& members = item->data_type.struct_members;
  if (!members.empty()) {
    CheckPatternKeys(item, members, diag_);
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto td = typedefs_.find(item->data_type.type_name);
  if (td == typedefs_.end() || td->second.struct_members.empty()) return;
  CheckPatternKeys(item, td->second.struct_members, diag_);
}

// --- §6 validation helpers ---

std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

// §10.4.2: Walk through select/member-access chains to find the base variable.
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

// §10.4.2: It shall be illegal to make nonblocking assignments to elements of
// dynamically sized array variables.
static void CheckNbaDynamicArrayTarget(
    const Stmt* s,
    const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    auto name = LhsBaseName(s->lhs);
    if (!name.empty() && dyn_names.count(name) != 0) {
      diag.Error(s->range.start,
                 "nonblocking assignment to element of dynamic array");
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

static void CollectProcTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty()) out.emplace(name, s->range.start);
  }
  for (auto* sub : s->stmts) CollectProcTargets(sub, out);
  CollectProcTargets(s->then_branch, out);
  CollectProcTargets(s->else_branch, out);
  CollectProcTargets(s->body, out);
  CollectProcTargets(s->for_body, out);
  for (auto& ci : s->case_items) CollectProcTargets(ci.body, out);
}

// §6.6.8: interconnect nets cannot be targets of procedural continuous
// assignments (force/release/assign/deassign).
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

// §6.6.8: check if an expression tree contains an interconnect identifier.
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
  if (!ConstEvalInt(e->index_end).has_value())
    diag.Error(e->range.start,
               "indexed part-select width must be a constant expression");
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

// §6.6.8: interconnect nets cannot appear in continuous assignments.
void Elaborator::ValidateInterconnectContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  // §6.6.8: interconnect net cannot be LHS of continuous assignment.
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier &&
      interconnect_names_.count(item->assign_lhs->text)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in continuous assignment");
  }
  // §6.6.8: interconnect net cannot appear in RHS expression.
  if (ExprUsesInterconnect(item->assign_rhs, interconnect_names_)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in expression");
  }
}

// §10.9: LHS assignment patterns shall use positional notation only.
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

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);
    // §6.6.8: interconnect cannot be target of force/release/assign/deassign.
    CheckInterconnectProcContAssign(item->body, interconnect_names_, diag_);
    CheckProceduralAssignLhs(item->body, diag_);
    // §10.9: LHS assignment patterns must use positional notation.
    WalkStmtsForLhsPatternKeys(item->body, diag_);
  }
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateInterconnectContAssign(item);
  ValidateClassHandleContAssign(item);
  // §6.3.2.2: Drive strength on a net declaration requires an initializer.
  if (item->kind == ModuleItemKind::kNetDecl &&
      (item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      !item->init_expr) {
    diag_.Error(item->loc,
                "drive strength on net declaration requires an assignment");
  }
  // §10.3.4: (highz0, highz1) and (highz1, highz0) are illegal.
  if (item->kind == ModuleItemKind::kNetDecl &&
      item->drive_strength0 == 1 && item->drive_strength1 == 1) {
    diag_.Error(item->loc, "drive strength (highz0, highz1) is illegal");
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
    CheckScalarSelect(item->assign_rhs, scalar_var_names_, diag_);
    CheckScalarSelect(item->assign_lhs, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidth(item->assign_rhs, diag_);
    CheckIndexedPartSelectWidth(item->assign_lhs, diag_);
    // §10.3.4: (highz0, highz1) and (highz1, highz0) are illegal.
    if (item->drive_strength0 == 1 && item->drive_strength1 == 1) {
      diag_.Error(item->loc, "drive strength (highz0, highz1) is illegal");
    }
  }
  if (is_proc && item->body) {
    CheckScalarSelectStmt(item->body, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidthStmt(item->body, diag_);
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

// §9.6.2 R8: Recursively check for disable statements targeting functions.
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

// §6.20.2: Check whether an expression contains a hierarchical reference.
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
  // §6.20.2: Body value parameters must have a default value.
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    // Skip type parameters (§6.20.3).
    if (item->data_type.kind == DataTypeKind::kVoid &&
        item->typedef_type.kind != DataTypeKind::kImplicit)
      continue;
    if (!item->init_expr) {
      diag_.Error(item->loc,
                  std::format("value parameter '{}' has no default value",
                              item->name));
      continue;
    }
    // §6.20.2: Parameter value shall not contain hierarchical references.
    if (ExprContainsHierRef(item->init_expr)) {
      diag_.Error(item->loc,
                  std::format("parameter '{}' value contains a hierarchical "
                              "reference",
                              item->name));
    }
    // §10.9: constant_assignment_pattern_expression elements must be constant.
    if (item->is_localparam &&
        item->init_expr->kind == ExprKind::kAssignmentPattern &&
        !IsConstantExpr(item->init_expr, BuildParamScope(mod))) {
      diag_.Error(item->loc,
                  std::format("localparam '{}' initializer is not a constant "
                              "expression",
                              item->name));
    }
  }
  // §6.20.2: Port list parameter values must also be constant.
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

// §9.3.2: Return statement inside a fork-join block is illegal.
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

// §9.3.2: Check if an expression references any name from a set.
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

// §9.3.2: Check a statement tree for references to ref arguments.
// is_fork_block_item: true for top-level fork block_item_declarations whose
// initializers are exempt from the restriction.
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

// §9.3.2: In fork-join_any/join_none, ref args (not ref static) are illegal
// except in block_item_declaration initializers.
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

// §13.2/§13.4.1/§13.4.4: Check function body for illegal constructs.
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
  // §13.2: Function shall not contain time-controlling statements.
  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kCycleDelay ||
      s->kind == StmtKind::kEventControl ||
      s->kind == StmtKind::kTimingControl || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitFork || s->kind == StmtKind::kWaitOrder) {
    diag.Error(s->range.start,
               "time-controlling statement is not allowed inside a function");
  }
  // §13.2: A function cannot enable a task.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall &&
      task_names.count(s->expr->callee) != 0) {
    diag.Error(s->range.start, "function cannot enable a task");
  }
  // §13.4.1: Illegal to declare variable with same name as function inside
  // body.
  if (s->kind == StmtKind::kVarDecl && !func_name.empty() &&
      s->var_name == func_name) {
    diag.Error(s->range.start,
               std::format("declaration of '{}' conflicts with function name",
                           func_name));
  }
  // §13.4.2: Static variable initializer must be a constant expression.
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
  // §9.3.2: Return is illegal inside any fork-join body.
  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
  // §13.4.4: fork/join_none body follows task rules, not function rules.
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

// §13.2: A task shall not return a value.
// §13.3.2: Automatic task variables shall not appear in nonblocking
// assignments.
static void CheckTaskBodyStmt(
    const Stmt* s,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn && s->expr) {
    diag.Error(s->range.start, "task returns a value");
  }
  // §13.3.2: Automatic task variables shall not use nonblocking assignments.
  if (s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kIdentifier &&
      auto_vars.count(s->lhs->text) != 0) {
    diag.Error(s->range.start,
               "automatic task variable in nonblocking assignment");
  }
  // §6.21: Automatic variables shall not be written by procedural continuous
  // assignments (force/release/assign/deassign).
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
  // §9.3.2: Return is illegal inside any fork-join body.
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

// §13.3.2: Collect names of variables that are automatic within a task body.
static void CollectAutoVarNames(const Stmt* s, bool task_is_auto,
                                std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    // In an automatic task, all locals are automatic unless explicitly static.
    // In a static task, only explicitly automatic locals are automatic.
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
  // §8.30.1: Validate weak_reference type parameter on function/task arguments.
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

  // §9.3.2: Ref args (not ref static) restricted in fork-join_any/join_none.
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
    // §13.3.2: Collect automatic variable names in the task.
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

// §13.4.3: Check if a function body contains fork constructs.
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

// §13.4.3: Check if a function body contains nonblocking assignments.
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

// §13.4.3: Validate that a function meets constant function constraints.
static bool ValidateConstantFunction(const ModuleItem* func, SourceLoc loc,
                                     DiagEngine& diag) {
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
  }
  return true;
}

// §13.4.3: Find function calls in an expression and validate for constant use.
static void ValidateConstantFuncCallsInExpr(
    const Expr* expr, SourceLoc loc,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    if (it != func_decls.end()) {
      ValidateConstantFunction(it->second, loc, diag);
    }
  }
  ValidateConstantFuncCallsInExpr(expr->lhs, loc, func_decls, diag);
  ValidateConstantFuncCallsInExpr(expr->rhs, loc, func_decls, diag);
  ValidateConstantFuncCallsInExpr(expr->condition, loc, func_decls, diag);
  ValidateConstantFuncCallsInExpr(expr->true_expr, loc, func_decls, diag);
  ValidateConstantFuncCallsInExpr(expr->false_expr, loc, func_decls, diag);
  for (auto* arg : expr->args)
    ValidateConstantFuncCallsInExpr(arg, loc, func_decls, diag);
  for (auto* elem : expr->elements)
    ValidateConstantFuncCallsInExpr(elem, loc, func_decls, diag);
}

// §13.4.3: Recursively scan module items for constant function calls in
// parameter initializers and generate conditions.
static void ValidateConstFuncCallsInItems(
    const std::vector<ModuleItem*>& items,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      ValidateConstantFuncCallsInExpr(item->init_expr, item->loc, func_decls,
                                      diag);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor) {
      if (item->gen_cond) {
        ValidateConstantFuncCallsInExpr(item->gen_cond, item->loc, func_decls,
                                        diag);
      }
      ValidateConstFuncCallsInItems(item->gen_body, func_decls, diag);
      if (item->gen_else) {
        ValidateConstFuncCallsInItems(item->gen_else->gen_body, func_decls,
                                      diag);
      }
      for (const auto& ci : item->gen_case_items) {
        ValidateConstFuncCallsInItems(ci.body, func_decls, diag);
      }
    }
  }
}

void Elaborator::ValidateConstantFunctionCalls(const ModuleDecl* decl) {
  // Check function calls in module header parameter defaults.
  for (const auto& [name, default_expr] : decl->params) {
    if (default_expr) {
      ValidateConstantFuncCallsInExpr(default_expr, decl->range.start,
                                      func_decls_, diag_);
    }
  }
  ValidateConstFuncCallsInItems(decl->items, func_decls_, diag_);
}

// §13.5: Check if an expression is a valid LHS for output/inout args.
static bool IsValidOutputArg(const Expr* e) {
  if (!e) return false;
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

// §13.5: Check whether parameter i is provided by the call expression.
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

// §13.5.3: Check that required args (no default) are provided.
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

// §13.5.4: Check that named args reference valid parameter names.
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

// §13.5: Find the call-site arg index for a named/positional parameter.
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

// §13.5: Check output/inout args are valid LHS.
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

// §13.5: Validate a single call expression against its declaration.
static void CheckCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
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
}

// §13.4.1: A void function cannot be used as an expression operand.
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

// §13.5: Walk expression tree for call validation.
static void WalkExprForCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  CheckCallArgs(expr, func_decls, diag);
  WalkExprForCallArgs(expr->lhs, func_decls, diag);
  WalkExprForCallArgs(expr->rhs, func_decls, diag);
  WalkExprForCallArgs(expr->condition, func_decls, diag);
  WalkExprForCallArgs(expr->true_expr, func_decls, diag);
  WalkExprForCallArgs(expr->false_expr, func_decls, diag);
  for (auto* a : expr->args) WalkExprForCallArgs(a, func_decls, diag);
  for (auto* e : expr->elements) WalkExprForCallArgs(e, func_decls, diag);
}

// §13.5: Walk statement tree for call validation.
static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!s) return;
  // §13.5 footnote 42: bare identifier call must be a task or void function.
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
      }
    }
  }
  // §13.4.1: Void function calls are legal only as standalone statements.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall) {
    for (auto* a : s->expr->args) CheckVoidCallInExpr(a, func_decls, diag);
  } else {
    CheckVoidCallInExpr(s->expr, func_decls, diag);
  }
  CheckVoidCallInExpr(s->rhs, func_decls, diag);
  CheckVoidCallInExpr(s->condition, func_decls, diag);
  CheckVoidCallInExpr(s->for_cond, func_decls, diag);
  WalkExprForCallArgs(s->expr, func_decls, diag);
  WalkExprForCallArgs(s->lhs, func_decls, diag);
  WalkExprForCallArgs(s->rhs, func_decls, diag);
  WalkExprForCallArgs(s->condition, func_decls, diag);
  for (auto* sub : s->stmts) WalkStmtForCallArgs(sub, func_decls, diag);
  WalkStmtForCallArgs(s->then_branch, func_decls, diag);
  WalkStmtForCallArgs(s->else_branch, func_decls, diag);
  WalkStmtForCallArgs(s->body, func_decls, diag);
  for (auto* fi : s->for_inits) WalkStmtForCallArgs(fi, func_decls, diag);
  WalkStmtForCallArgs(s->for_body, func_decls, diag);
  for (auto* fs : s->for_steps) WalkStmtForCallArgs(fs, func_decls, diag);
  WalkExprForCallArgs(s->for_cond, func_decls, diag);
  for (auto& ci : s->case_items) WalkStmtForCallArgs(ci.body, func_decls, diag);
}

void Elaborator::ValidateSubroutineCallArgs(const ModuleDecl* decl) {
  // Build combined map of tasks and functions.
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      WalkStmtForCallArgs(item->body, all_decls, diag_);
    }
    // Also check function/task bodies.
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        WalkStmtForCallArgs(s, all_decls, diag_);
      }
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckVoidCallInExpr(item->assign_rhs, all_decls, diag_);
    }
  }
}

// =============================================================================
// §14.3 — Clocking block declaration validation
// =============================================================================

void Elaborator::ValidateClockingBlock(ModuleItem* item) {
  // §14.3: Only default clocking blocks may be unnamed.
  if (item->name.empty() && !item->is_default_clocking) {
    diag_.Error(item->loc, "non-default clocking block must have a name");
  }
  // Register clocking signals for direction tracking.
  if (!item->name.empty()) {
    auto& sigs = clocking_signals_[item->name];
    for (const auto& sig : item->clocking_signals) {
      sigs[sig.name] = {sig.direction};
    }
  }
}

// §14.3: Check a single expression for clockvar access direction violations.
void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier) {
    auto block_it = clocking_signals_.find(e->lhs->text);
    if (block_it != clocking_signals_.end()) {
      // Determine the member name from rhs or text.
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
  // Recurse into sub-expressions (rvalue context).
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
    CheckClockvarAccessExpr(s->lhs, /*is_lvalue=*/true);
    CheckClockvarAccessExpr(s->rhs, /*is_lvalue=*/false);
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

// §14.11: Check if any procedural statement uses ## cycle delay.
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

// §14.12: At most one default clocking per module/interface/program/checker.
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

// §14.14: At most one global clocking per module/interface/program/checker.
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

// §14.16: Continuous assignment to a clocking output variable is illegal.
void Elaborator::ValidateContAssignToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs || item->assign_lhs->kind != ExprKind::kIdentifier)
      continue;
    auto target = item->assign_lhs->text;
    for (const auto& [block_name, sigs] : clocking_signals_) {
      auto it = sigs.find(target);
      if (it != sigs.end() &&
          (it->second.direction == Direction::kOutput ||
           it->second.direction == Direction::kInout)) {
        diag_.Error(item->loc,
                    std::format("continuous assignment to clocking output "
                                "variable '{}'",
                                target));
        break;
      }
    }
  }
}

// §9.4.2.4: Walk a statement tree marking sequence events and checking R5.
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
        // R5: Arguments to a sequence instance in an event expression
        // shall be static — automatic variables are illegal.
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
    // R5: Check tasks — automatic tasks cannot pass automatic vars.
    if (item->kind == ModuleItemKind::kTaskDecl && item->body) {
      WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                 sequence_names_, item->is_automatic, diag_);
    }
  }
}

}  // namespace delta
