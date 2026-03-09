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

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

// §7.6: Check a single continuous assignment for array compatibility.
void Elaborator::ValidateOneArrayAssignment(const ModuleItem* item) {
  if (!item->assign_lhs || !item->assign_rhs) return;
  if (item->assign_lhs->kind != ExprKind::kIdentifier) return;
  if (item->assign_rhs->kind != ExprKind::kIdentifier) return;
  auto lhs_it = var_array_info_.find(item->assign_lhs->text);
  auto rhs_it = var_array_info_.find(item->assign_rhs->text);
  if (lhs_it == var_array_info_.end() || rhs_it == var_array_info_.end())
    return;
  const auto& lhs = lhs_it->second;
  const auto& rhs = rhs_it->second;
  // §7.9.9
  if (lhs.is_assoc != rhs.is_assoc) {
    diag_.Error(item->loc,
                "associative array cannot be assigned to or from a "
                "non-associative array");
    return;
  }
  if (lhs.is_assoc && rhs.is_assoc &&
      lhs.assoc_index_type != rhs.assoc_index_type) {
    diag_.Error(item->loc,
                "associative array index type mismatch in assignment");
    return;
  }
  if (lhs.elem_type != rhs.elem_type) {
    diag_.Error(item->loc,
                std::format("array element type mismatch in assignment "
                            "('{}' vs '{}')",
                            item->assign_lhs->text, item->assign_rhs->text));
    return;
  }
  if (lhs.unpacked_size > 0 && !lhs.is_dynamic && rhs.unpacked_size > 0 &&
      !rhs.is_dynamic && lhs.unpacked_size != rhs.unpacked_size) {
    diag_.Error(item->loc,
                std::format("array size mismatch: '{}' has {} elements but "
                            "'{}' has {}",
                            item->assign_lhs->text, lhs.unpacked_size,
                            item->assign_rhs->text, rhs.unpacked_size));
  }
}

// §7.6: Validate array assignment compatibility in continuous assignments.
void Elaborator::ValidateArrayAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    ValidateOneArrayAssignment(item);
  }
}

// §7.8.5: real/shortreal shall be an illegal associative array index type.
void Elaborator::ValidateAssocIndexType(const ModuleItem* item) {
  if (item->unpacked_dims.empty()) return;
  auto* dim = item->unpacked_dims[0];
  if (!dim || dim->kind != ExprKind::kIdentifier) return;
  auto t = dim->text;
  if (t == "real" || t == "shortreal" || t == "realtime") {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
  }
}

// --- §8.4: Class handle operator restriction validation ---

static bool IsClassVar(const Expr* e,
                       const std::unordered_set<std::string_view>& class_vars) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  return class_vars.count(name) != 0;
}

// §8.4 Table 8-1: Only ==, !=, ===, !== are legal binary ops on class handles.
static bool IsAllowedClassBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

static void CheckClassHandleExpr(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    DiagEngine& diag) {
  if (!e) return;
  // Binary: only equality operators are allowed.
  if (e->kind == ExprKind::kBinary) {
    bool lhs_class = e->lhs && IsClassVar(e->lhs, class_vars);
    bool rhs_class = e->rhs && IsClassVar(e->rhs, class_vars);
    if ((lhs_class || rhs_class) && !IsAllowedClassBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on class object handles");
    }
  }
  // Unary: no unary operators are allowed on class handles.
  if (e->kind == ExprKind::kUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }
  // Postfix (++, --): not allowed.
  if (e->kind == ExprKind::kPostfixUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }
  // Bit-select on class handle is illegal.
  if (e->kind == ExprKind::kSelect && e->base &&
      IsClassVar(e->base, class_vars)) {
    diag.Error(e->range.start, "bit-select on class object handle is illegal");
  }
  // Recurse into sub-expressions.
  CheckClassHandleExpr(e->lhs, class_vars, diag);
  CheckClassHandleExpr(e->rhs, class_vars, diag);
  CheckClassHandleExpr(e->base, class_vars, diag);
  CheckClassHandleExpr(e->index, class_vars, diag);
  CheckClassHandleExpr(e->condition, class_vars, diag);
  CheckClassHandleExpr(e->true_expr, class_vars, diag);
  CheckClassHandleExpr(e->false_expr, class_vars, diag);
  for (const auto* elem : e->elements) {
    CheckClassHandleExpr(elem, class_vars, diag);
  }
}

void Elaborator::WalkStmtsForClassHandleOps(const Stmt* s) {
  if (!s) return;
  // Check compound assignment to class handle.
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && IsClassVar(s->lhs, class_var_names_)) {
    if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
        IsCompoundAssignOp(s->rhs->op)) {
      diag_.Error(s->range.start,
                  "operator is not allowed on class object handles");
    }
  }
  // Check expressions in assignments, conditions, and expression statements.
  CheckClassHandleExpr(s->rhs, class_var_names_, diag_);
  CheckClassHandleExpr(s->expr, class_var_names_, diag_);
  CheckClassHandleExpr(s->condition, class_var_names_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForClassHandleOps(sub);
  WalkStmtsForClassHandleOps(s->then_branch);
  WalkStmtsForClassHandleOps(s->else_branch);
  WalkStmtsForClassHandleOps(s->body);
  WalkStmtsForClassHandleOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForClassHandleOps(ci.body);
}

void Elaborator::ValidateClassHandleOps(const ModuleDecl* decl) {
  if (class_var_names_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForClassHandleOps(item->body);
    }
  }
}

void Elaborator::ValidateClassHandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  auto lhs_class =
      item->assign_lhs && IsClassVar(item->assign_lhs, class_var_names_);
  auto rhs_class =
      item->assign_rhs && IsClassVar(item->assign_rhs, class_var_names_);
  if (lhs_class || rhs_class) {
    diag_.Error(item->loc,
                "class object handle cannot be used in continuous assignment");
  }
}

// §8.10: Check if an expression references 'this' or 'super'.
static bool ExprRefsThisOrSuper(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier &&
      (e->text == "this" || e->text == "super"))
    return true;
  if (ExprRefsThisOrSuper(e->lhs)) return true;
  if (ExprRefsThisOrSuper(e->rhs)) return true;
  if (ExprRefsThisOrSuper(e->base)) return true;
  if (ExprRefsThisOrSuper(e->index)) return true;
  if (ExprRefsThisOrSuper(e->condition)) return true;
  if (ExprRefsThisOrSuper(e->true_expr)) return true;
  if (ExprRefsThisOrSuper(e->false_expr)) return true;
  for (const auto* elem : e->elements) {
    if (ExprRefsThisOrSuper(elem)) return true;
  }
  return false;
}

// §8.10: Walk statements looking for 'this'/'super' references.
static bool StmtRefsThisOrSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsThisOrSuper(s->lhs)) return true;
  if (ExprRefsThisOrSuper(s->rhs)) return true;
  if (ExprRefsThisOrSuper(s->expr)) return true;
  if (ExprRefsThisOrSuper(s->condition)) return true;
  for (auto* sub : s->stmts) {
    if (StmtRefsThisOrSuper(sub)) return true;
  }
  if (StmtRefsThisOrSuper(s->then_branch)) return true;
  if (StmtRefsThisOrSuper(s->else_branch)) return true;
  if (StmtRefsThisOrSuper(s->body)) return true;
  if (StmtRefsThisOrSuper(s->for_body)) return true;
  for (auto& ci : s->case_items) {
    if (StmtRefsThisOrSuper(ci.body)) return true;
  }
  return false;
}

// §8.10: Check a single class for static methods referencing this/super.
void Elaborator::ValidateOneClassStaticMethods(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsThisOrSuper(s)) {
        diag_.Error(m->method->loc,
                    "'this' and 'super' shall not be used in "
                    "a static method");
        break;
      }
    }
  }
}

void Elaborator::ValidateStaticMethodBodies(const ModuleDecl* decl) {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassStaticMethods(cls);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      ValidateOneClassStaticMethods(item->class_decl);
    }
  }
}

// §8.11: Check a single module item for illegal 'this' usage.
void Elaborator::ValidateThisInItem(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body && StmtRefsThisOrSuper(item->body)) {
    diag_.Error(item->loc,
                "'this' shall only be used within non-static class methods");
    return;
  }
  bool is_func_or_task = item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kTaskDecl;
  if (!is_func_or_task || item->func_body_stmts.empty()) return;
  for (const auto* s : item->func_body_stmts) {
    if (StmtRefsThisOrSuper(s)) {
      diag_.Error(item->loc,
                  "'this' shall only be used within non-static "
                  "class methods");
      return;
    }
  }
}

// §8.11: 'this' shall only be used within non-static class methods.
void Elaborator::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateThisInItem(item);
  }
}

// §8.13: A class declared :final shall not be extended.
void Elaborator::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
    }
  };
  for (const auto* cls : unit_->classes) {
    check(cls);
  }
}

// §8.17: Detect if a statement is a super.new() call.
static bool IsSuperNewCall(const Stmt* s) {
  if (!s || s->kind != StmtKind::kExprStmt || !s->expr) return false;
  const auto* call = s->expr;
  if (call->kind != ExprKind::kCall) return false;
  const auto* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  bool lhs_is_super = callee->lhs &&
                      callee->lhs->kind == ExprKind::kIdentifier &&
                      callee->lhs->text == "super";
  bool rhs_is_new = callee->rhs && callee->rhs->kind == ExprKind::kIdentifier &&
                    callee->rhs->text == "new";
  return lhs_is_super && rhs_is_new;
}

// §8.17: Validate chaining constructor rules for a single class.
void Elaborator::ValidateOneClassChainingCtor(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const ClassMember* ctor = nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      ctor = m;
      break;
    }
  }
  if (!ctor || !ctor->method) return;
  bool has_super_new = false;
  const auto& stmts = ctor->method->func_body_stmts;
  for (size_t i = 0; i < stmts.size(); ++i) {
    if (!IsSuperNewCall(stmts[i])) continue;
    has_super_new = true;
    if (i != 0) {
      diag_.Error(stmts[i]->range.start,
                  "super.new() shall be the first executable statement "
                  "in the constructor");
    }
    break;
  }
  if (has_super_new && !cls->extends_args.empty()) {
    diag_.Error(ctor->method->loc,
                "constructor shall not contain super.new() when extends "
                "specifier has arguments");
  }
}

// §8.17: Validate chaining constructor rules.
void Elaborator::ValidateChainingConstructors() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassChainingCtor(cls);
  }
}

// §8.18: Find a class member by name, walking up the hierarchy.
static const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c; /* advance below */) {
    for (const auto* m : c->members) {
      if (m->name == name) return m;
    }
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return nullptr;
}

// §8.18: Check a single obj.member access for visibility violations.
static void CheckMemberAccessVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (e->lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types.find(e->lhs->text);
  if (it == var_types.end()) return;
  if (e->rhs->kind != ExprKind::kIdentifier) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls) return;
  const auto* m = FindMemberInClass(cls, e->rhs->text, unit);
  if (m && m->is_local) {
    diag.Error(e->rhs->range.start,
               "cannot access local member from outside its class");
  } else if (m && m->is_protected) {
    diag.Error(e->rhs->range.start,
               "cannot access protected member from outside "
               "its class hierarchy");
  }
}

// §8.18: Check expressions for local/protected member access from outside
// class.
static void CheckVisibilityExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs) {
    CheckMemberAccessVisibility(e, var_types, unit, diag);
  }
  CheckVisibilityExpr(e->lhs, var_types, unit, diag);
  CheckVisibilityExpr(e->rhs, var_types, unit, diag);
  CheckVisibilityExpr(e->base, var_types, unit, diag);
  CheckVisibilityExpr(e->index, var_types, unit, diag);
  CheckVisibilityExpr(e->condition, var_types, unit, diag);
  CheckVisibilityExpr(e->true_expr, var_types, unit, diag);
  CheckVisibilityExpr(e->false_expr, var_types, unit, diag);
  for (const auto* arg : e->args)
    CheckVisibilityExpr(arg, var_types, unit, diag);
}

// §8.18: Walk statements checking for local/protected access violations.
static void WalkStmtsForVisibility(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVisibilityExpr(s->lhs, var_types, unit, diag);
  CheckVisibilityExpr(s->rhs, var_types, unit, diag);
  CheckVisibilityExpr(s->expr, var_types, unit, diag);
  CheckVisibilityExpr(s->condition, var_types, unit, diag);
  for (auto* sub : s->stmts) WalkStmtsForVisibility(sub, var_types, unit, diag);
  WalkStmtsForVisibility(s->then_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->else_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->body, var_types, unit, diag);
  WalkStmtsForVisibility(s->for_body, var_types, unit, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForVisibility(ci.body, var_types, unit, diag);
}

// §8.18: Validate local/protected access from module-level code.
void Elaborator::ValidateLocalProtectedAccess(const ModuleDecl* decl) {
  if (class_var_types_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForVisibility(item->body, class_var_types_, unit_, diag_);
    }
  }
}

// §8.19: Validate constant class property rules.
void Elaborator::ValidateConstClassProperties() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kProperty || !m->is_const) continue;
      if (!m->init_expr && m->is_static) {
        diag_.Error(m->loc, "instance constant cannot be declared static");
      }
    }
  }
}

// §8.20: Find a virtual method in a base class by name.
static const ClassMember* FindBaseVirtualMethod(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && m->is_virtual) {
        return m;
      }
    }
  }
  return nullptr;
}

// §8.20: Validate a single method's override rules within a class.
void Elaborator::ValidateOneMethodOverride(const ClassDecl* cls,
                                           const ClassMember* m) {
  auto* method = m->method;
  if (method->is_method_initial && method->is_method_extends) {
    diag_.Error(method->loc,
                "':initial' and ':extends' are mutually exclusive");
    return;
  }
  const auto* base_virtual = FindBaseVirtualMethod(cls, method->name, unit_);
  if (method->is_method_initial && base_virtual) {
    diag_.Error(method->loc,
                "method with ':initial' shall not override a virtual "
                "base class method");
  }
  if (method->is_method_extends && !base_virtual) {
    diag_.Error(method->loc,
                "method with ':extends' does not override a virtual "
                "base class method");
  }
  if (base_virtual && base_virtual->method &&
      base_virtual->method->is_method_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'");
  }
}

// §8.20: Validate virtual method override rules.
void Elaborator::ValidateVirtualMethodOverrides() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateOneMethodOverride(cls, m);
    }
  }
}

// §8.21: Collect all pure virtual method names from a class and its ancestors.
static void CollectPureVirtualMethods(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    CollectPureVirtualMethods(base, unit, pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->method->name);
    } else if (m->is_virtual) {
      std::erase(pure_names, m->method->name);
    }
  }
}

// §8.21: Check that a non-abstract class implements all pure virtual methods.
void Elaborator::ValidateAbstractClassUnimplemented(const ClassDecl* cls) {
  if (cls->is_virtual || cls->base_class.empty()) return;
  std::vector<std::string_view> unimpl;
  CollectPureVirtualMethods(cls, unit_, unimpl);
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "pure virtual method '{}'",
                            cls->name, name));
  }
}

// §8.21: Validate abstract class and pure virtual method rules.
void Elaborator::ValidateAbstractClassRules() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      if (m->is_pure_virtual && m->method->is_method_final) {
        diag_.Error(m->method->loc,
                    "':final' shall not be specified on a pure virtual method");
      }
    }
    ValidateAbstractClassUnimplemented(cls);
  }
}

// §8.24: Validate out-of-block method declarations.
void Elaborator::ValidateOutOfBlockDeclarations() {
  std::unordered_set<std::string> linked;
  for (auto* item : unit_->cu_items) {
    if (item->method_class.empty()) continue;
    bool is_func = (item->kind == ModuleItemKind::kFunctionDecl);
    bool is_task = (item->kind == ModuleItemKind::kTaskDecl);
    if (!is_func && !is_task) continue;
    const auto* cls = FindClassDecl(item->method_class, unit_);
    if (!cls) {
      diag_.Error(item->loc,
                  std::format("out-of-block declaration for unknown class '{}'",
                              item->method_class));
      continue;
    }
    bool found_proto = false;
    for (auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      if (m->method->name != item->name) continue;
      if (!m->method->is_extern) continue;
      found_proto = true;
      break;
    }
    if (!found_proto) {
      diag_.Error(
          item->loc,
          std::format("no matching extern prototype for '{}::{}' in "
                      "class '{}'",
                      item->method_class, item->name, item->method_class));
      continue;
    }
    auto key = std::string(item->method_class) + "::" + std::string(item->name);
    if (linked.count(key)) {
      diag_.Error(item->loc,
                  std::format("duplicate out-of-block declaration for '{}::{}'",
                              item->method_class, item->name));
      continue;
    }
    linked.insert(key);
  }
}

// §8.26.1: Validate members of an interface class.
void Elaborator::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
      diag_.Error(m->method ? m->method->loc : cls->range.start,
                  std::format("interface class '{}' shall only contain "
                              "pure virtual methods",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kProperty && !m->is_const) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "data members",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kConstraint) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "constraint blocks",
                              cls->name));
    }
  }
}

// §8.26.2: Validate inheritance rules for an interface class.
void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name));
  }
  if (cls->base_class.empty()) return;
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class));
  }
}

// §8.26.2: Validate that a regular class does not extend an interface class.
void Elaborator::ValidateRegularClassInheritance(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("class '{}' cannot extend interface class "
                            "'{}'; use 'implements' instead",
                            cls->name, cls->base_class));
  }
}

// §8.26: Check whether a class hierarchy has a concrete virtual method.
static bool HasConcreteVirtualMethodInHierarchy(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name && cm->is_virtual) {
      return true;
    }
  }
  if (cls->base_class.empty()) return false;
  const auto* walk = FindClassDecl(cls->base_class, unit);
  while (walk) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          !bm->is_pure_virtual) {
        return true;
      }
    }
    walk = walk->base_class.empty() ? nullptr
                                    : FindClassDecl(walk->base_class, unit);
  }
  return false;
}

// §8.26: Validate that a non-abstract class implements all interface methods.
void Elaborator::ValidateImplementsInterfaceMethods(const ClassDecl* cls) {
  if (cls->is_virtual || cls->implements_types.empty()) return;
  for (auto iface_name : cls->implements_types) {
    const auto* iface = FindClassDecl(iface_name, unit_);
    if (!iface) continue;
    for (const auto* im : iface->members) {
      if (im->kind != ClassMemberKind::kMethod || !im->is_pure_virtual)
        continue;
      if (!im->method) continue;
      if (!HasConcreteVirtualMethodInHierarchy(cls, im->method->name, unit_)) {
        diag_.Error(cls->range.start,
                    std::format("class '{}' does not implement pure virtual "
                                "method '{}' from interface '{}'",
                                cls->name, im->method->name, iface_name));
      }
    }
  }
}

// §8.26: Validate interface class rules.
void Elaborator::ValidateInterfaceClassRules() {
  for (const auto* cls : unit_->classes) {
    if (cls->is_interface) {
      ValidateInterfaceClassMembers(cls);
      ValidateInterfaceClassInheritance(cls);
    } else {
      ValidateRegularClassInheritance(cls);
      ValidateImplementsInterfaceMethods(cls);
    }
  }
}

// --- §11.2.2: Aggregate expression comparison validation ---

// §11.2.2: Check a single binary expression for aggregate type mismatch.
void Elaborator::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  if (expr->rhs->kind != ExprKind::kIdentifier) return;
  auto lit = var_named_types_.find(expr->lhs->text);
  auto rit = var_named_types_.find(expr->rhs->text);
  if (lit == var_named_types_.end() || rit == var_named_types_.end()) return;
  if (lit->second == rit->second) return;
  diag_.Error(expr->range.start,
              std::format("comparison of non-equivalent aggregate "
                          "types '{}' and '{}'",
                          lit->second, rit->second));
}

void Elaborator::WalkExprForAggregateCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary &&
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq)) {
    CheckAggregateCompareOp(expr);
  }
  WalkExprForAggregateCompare(expr->lhs);
  WalkExprForAggregateCompare(expr->rhs);
  WalkExprForAggregateCompare(expr->condition);
  WalkExprForAggregateCompare(expr->true_expr);
  WalkExprForAggregateCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForAggregateCompare(elem);
  for (auto* arg : expr->args) WalkExprForAggregateCompare(arg);
}

void Elaborator::WalkStmtsForAggregateCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForAggregateCompare(s->rhs);
  WalkExprForAggregateCompare(s->lhs);
  WalkExprForAggregateCompare(s->expr);
  WalkExprForAggregateCompare(s->condition);
  WalkExprForAggregateCompare(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForAggregateCompare(sub);
  WalkStmtsForAggregateCompare(s->then_branch);
  WalkStmtsForAggregateCompare(s->else_branch);
  WalkStmtsForAggregateCompare(s->body);
  WalkStmtsForAggregateCompare(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAggregateCompare(ci.body);
}

void Elaborator::ValidateAggregateComparisons(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForAggregateCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAggregateCompare(item->assign_rhs);
    }
  }
}

// --- §11.3.1: Operators not permitted on real operands ---

static bool IsRealVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && IsRealType(it->second);
}

// Operators illegal on real/shortreal operands per Table 11-1.
static bool IsIllegalOnReal(TokenKind op) {
  switch (op) {
    // Case equality
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    // Wildcard equality
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
    // Bitwise binary
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
    // Shift
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
    // Modulus
    case TokenKind::kPercent:
      return true;
    default:
      return false;
  }
}

// Unary operators illegal on real operands.
static bool IsUnaryIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

void Elaborator::WalkExprForRealOps(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool lhs_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    bool rhs_real = expr->rhs && IsRealVar(expr->rhs, var_types_);
    if ((lhs_real || rhs_real) && IsIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  if (expr->kind == ExprKind::kUnary) {
    bool operand_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    if (operand_real && IsUnaryIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  "operator is not allowed on real operands");
    }
  }
  WalkExprForRealOps(expr->lhs);
  WalkExprForRealOps(expr->rhs);
  WalkExprForRealOps(expr->condition);
  WalkExprForRealOps(expr->true_expr);
  WalkExprForRealOps(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForRealOps(elem);
  for (auto* arg : expr->args) WalkExprForRealOps(arg);
}

void Elaborator::WalkStmtsForRealOps(const Stmt* s) {
  if (!s) return;
  WalkExprForRealOps(s->rhs);
  WalkExprForRealOps(s->lhs);
  WalkExprForRealOps(s->expr);
  WalkExprForRealOps(s->condition);
  WalkExprForRealOps(s->assert_expr);
  for (auto* sub : s->stmts) WalkStmtsForRealOps(sub);
  WalkStmtsForRealOps(s->then_branch);
  WalkStmtsForRealOps(s->else_branch);
  WalkStmtsForRealOps(s->body);
  WalkStmtsForRealOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForRealOps(ci.body);
}

void Elaborator::ValidateRealOperatorRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForRealOps(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForRealOps(item->assign_rhs);
    }
  }
}

// --- §11.3.6: Assignment-in-expression restrictions ---

void Elaborator::WalkExprForAssignInExpr(const Expr* expr,
                                         bool in_event_or_cont) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary && expr->op == TokenKind::kEq) {
    if (in_event_or_cont) {
      diag_.Error(expr->range.start,
                  "assignment operator within expression is illegal in "
                  "this context");
    }
  }
  WalkExprForAssignInExpr(expr->lhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->rhs, in_event_or_cont);
  WalkExprForAssignInExpr(expr->condition, in_event_or_cont);
  WalkExprForAssignInExpr(expr->true_expr, in_event_or_cont);
  WalkExprForAssignInExpr(expr->false_expr, in_event_or_cont);
  for (auto* elem : expr->elements)
    WalkExprForAssignInExpr(elem, in_event_or_cont);
  for (auto* arg : expr->args) WalkExprForAssignInExpr(arg, in_event_or_cont);
}

void Elaborator::WalkStmtsForAssignInExpr(const Stmt* s) {
  if (!s) return;
  for (auto* sub : s->stmts) WalkStmtsForAssignInExpr(sub);
  WalkStmtsForAssignInExpr(s->then_branch);
  WalkStmtsForAssignInExpr(s->else_branch);
  WalkStmtsForAssignInExpr(s->body);
  WalkStmtsForAssignInExpr(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForAssignInExpr(ci.body);
}

void Elaborator::ValidateAssignInExprRestrictions(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      for (const auto& ev : item->sensitivity) {
        WalkExprForAssignInExpr(ev.signal, true);
      }
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAssignInExpr(item->assign_rhs, true);
    }
  }
}

// §10.11: Validate alias statement operands.
static std::string_view AliasNetIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

void Elaborator::ValidateAlias(const ModuleItem* item) {
  std::unordered_set<std::string_view> seen;
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!seen.insert(name).second) {
      diag_.Error(item->loc, std::format("net '{}' aliased to itself", name));
    }
  }
  for (auto* net : item->alias_nets) {
    auto name = AliasNetIdent(net);
    if (name.empty()) continue;
    if (!net_names_.count(name) && declared_names_.count(name)) {
      diag_.Error(item->loc,
                  std::format("'{}' is a variable, not a net; "
                              "variables cannot appear in alias statements",
                              name));
    }
  }
}

// §10.10.3: Check a single assignment for nested concatenation in unpacked
// array context.
void Elaborator::CheckArrayConcatNestingInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.elem_type == DataTypeKind::kString) return;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kConcatenation) {
      diag_.Error(elem->range.start,
                  "nested concatenation in unpacked array "
                  "concatenation is not self-determined");
    }
  }
}

// §10.10.3: Validate nesting of unpacked array concatenations.
void Elaborator::WalkStmtsForArrayConcatNesting(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayConcatNestingInAssign(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayConcatNesting(sub);
  WalkStmtsForArrayConcatNesting(s->then_branch);
  WalkStmtsForArrayConcatNesting(s->else_branch);
  WalkStmtsForArrayConcatNesting(s->body);
  WalkStmtsForArrayConcatNesting(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayConcatNesting(ci.body);
}

void Elaborator::ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      WalkStmtsForArrayConcatNesting(item->body);
    }
  }
}

}  // namespace delta
