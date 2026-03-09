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
         key == "bit" || key == "real" || key == "shortreal" || key == "string";
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

static void CheckPatternCoverage(const ModuleItem* item,
                                 const std::vector<StructMember>& members,
                                 const std::unordered_set<std::string_view>& seen,
                                 DiagEngine& diag) {
  for (const auto& m : members) {
    if (!seen.count(m.name)) {
      diag.Error(item->loc,
                 std::format("member '{}' not covered by assignment pattern",
                             m.name));
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

// §6.6.8: interconnect nets cannot appear in continuous assignments.
void Elaborator::ValidateInterconnectContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (!item->assign_lhs || item->assign_lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  if (interconnect_names_.count(item->assign_lhs->text)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);
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
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
    // §10.3.4: (highz0, highz1) and (highz1, highz0) are illegal.
    if (item->drive_strength0 == 1 && item->drive_strength1 == 1) {
      diag_.Error(item->loc, "drive strength (highz0, highz1) is illegal");
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
  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kEventControl ||
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
  // §13.4.4: fork/join_none body follows task rules, not function rules.
  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;
  for (auto* sub : s->stmts)
    CheckFuncBodyStmt(sub, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->then_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->else_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->for_body, is_void, task_names, func_name, diag);
  for (auto& ci : s->case_items)
    CheckFuncBodyStmt(ci.body, is_void, task_names, func_name, diag);
}

// §13.2: A task shall not return a value.
// §13.3.2: Automatic task variables shall not appear in nonblocking
// assignments.
static void CheckTaskBodyStmt(
    const Stmt* s, bool is_auto,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn && s->expr) {
    diag.Error(s->range.start, "task returns a value");
  }
  // §13.3.2: Automatic task variables shall not use nonblocking assignments.
  if (is_auto && s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kIdentifier &&
      auto_vars.count(s->lhs->text) != 0) {
    diag.Error(s->range.start,
               "automatic task variable in nonblocking assignment");
  }
  // Collect locally declared variables as we descend.
  for (auto* sub : s->stmts) CheckTaskBodyStmt(sub, is_auto, auto_vars, diag);
  CheckTaskBodyStmt(s->then_branch, is_auto, auto_vars, diag);
  CheckTaskBodyStmt(s->else_branch, is_auto, auto_vars, diag);
  CheckTaskBodyStmt(s->body, is_auto, auto_vars, diag);
  CheckTaskBodyStmt(s->for_body, is_auto, auto_vars, diag);
  for (auto& ci : s->case_items)
    CheckTaskBodyStmt(ci.body, is_auto, auto_vars, diag);
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
      CheckTaskBodyStmt(s, is_auto, auto_vars, diag_);
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

void Elaborator::ValidateConstantFunctionCalls(const ModuleDecl* decl) {
  // Check function calls in module header parameter defaults.
  for (const auto& [name, default_expr] : decl->params) {
    if (default_expr) {
      ValidateConstantFuncCallsInExpr(default_expr, decl->range.start,
                                      func_decls_, diag_);
    }
  }
  // Check function calls in localparam/parameter item initializers.
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl || !item->init_expr) continue;
    ValidateConstantFuncCallsInExpr(item->init_expr, item->loc, func_decls_,
                                    diag_);
  }
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
  if (expr->arg_names.empty()) return (i < expr->args.size());
  if (i < positional_count) return true;
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
  WalkExprForCallArgs(s->expr, func_decls, diag);
  WalkExprForCallArgs(s->lhs, func_decls, diag);
  WalkExprForCallArgs(s->rhs, func_decls, diag);
  WalkExprForCallArgs(s->condition, func_decls, diag);
  for (auto* sub : s->stmts) WalkStmtForCallArgs(sub, func_decls, diag);
  WalkStmtForCallArgs(s->then_branch, func_decls, diag);
  WalkStmtForCallArgs(s->else_branch, func_decls, diag);
  WalkStmtForCallArgs(s->body, func_decls, diag);
  WalkStmtForCallArgs(s->for_init, func_decls, diag);
  WalkStmtForCallArgs(s->for_body, func_decls, diag);
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
  }
}

}  // namespace delta
