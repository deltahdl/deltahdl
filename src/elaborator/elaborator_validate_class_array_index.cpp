#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsLiteralExpr(ExprKind kind) {
  return kind == ExprKind::kIntegerLiteral || kind == ExprKind::kRealLiteral ||
         kind == ExprKind::kTimeLiteral || kind == ExprKind::kStringLiteral ||
         kind == ExprKind::kUnbasedUnsizedLiteral;
}

// §7.8.3: resolving a class-indexed select requires the elaboration context
// that describes the visible class-indexed associative arrays and class types
// of the enclosing scope. These values always travel together as one unit, so
// they are bundled into a single context object passed through the recursive
// walk. local_classes maps the names of classes declared inside the enclosing
// module to their declarations, which are not visible through unit->classes.
struct ClassIndexCtx {
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_map<std::string_view, const ClassDecl*>& local_classes;
  // Type kind of every declared variable in scope. Used to reject a
  // non-class-typed variable (e.g. an int or a string) used as a class index,
  // which class_var_types alone cannot see because it holds only class handles.
  const TypeMap& var_types;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

// Resolves a class name to its declaration, preferring a class declared inside
// the enclosing module (which FindClassDecl does not see, as those live in the
// module rather than in unit->classes) before falling back to compilation-unit
// scope.
static const ClassDecl* FindClassDeclScoped(std::string_view name,
                                            const ClassIndexCtx& ctx) {
  auto it = ctx.local_classes.find(name);
  if (it != ctx.local_classes.end()) return it->second;
  return FindClassDecl(name, ctx.unit);
}

// §7.8.3: true when class *a* is *b* or is derived (directly or transitively)
// from *b*. Walks the base-class chain consulting both module-local and
// compilation-unit class scopes so a class declared inside the module resolves.
static bool IsClassDerivedFromScoped(std::string_view a, std::string_view b,
                                     const ClassIndexCtx& ctx) {
  if (a == b) return true;
  for (const auto* cls = FindClassDeclScoped(a, ctx); cls;
       cls = cls->base_class.empty()
                 ? nullptr
                 : FindClassDeclScoped(cls->base_class, ctx)) {
    if (cls->base_class == b) return true;
  }
  return false;
}

// §7.8.3: an associative array declared with a class index may only be
// indexed by an object of that class or a class derived from it; a null
// handle is also valid. Any other index expression is a type error.
//
// Returns true when the index expression of a class-indexed associative array
// select is an illegal index (a literal, or an identifier whose class type is
// not the index class or a class derived from it).
static bool IsIllegalClassIndex(const Expr* idx, std::string_view index_class,
                                const ClassIndexCtx& ctx) {
  bool is_null = idx->kind == ExprKind::kIdentifier && idx->text == "null";
  if (is_null) return false;
  if (IsLiteralExpr(idx->kind)) return true;
  if (idx->kind == ExprKind::kIdentifier) {
    auto vt = ctx.class_var_types.find(idx->text);
    if (vt != ctx.class_var_types.end()) {
      // A class handle is legal only when its class is the index class or a
      // class derived from it; any other class is illegal.
      return !IsClassDerivedFromScoped(vt->second, index_class, ctx);
    }
    // Not a class-typed variable. A declared variable of a concrete non-class
    // type (an integral, string, real, etc. value, kind != kNamed) is "any
    // other type" and is therefore an illegal class index.
    auto gt = ctx.var_types.find(idx->text);
    if (gt != ctx.var_types.end() && gt->second != DataTypeKind::kNamed) {
      return true;
    }
  }
  return false;
}

// Validates a single select node against the class-index rule, emitting a
// diagnostic when its index expression is illegal. Non-select nodes are
// ignored.
static void CheckClassIndexSelectNode(const Expr* e, const ClassIndexCtx& ctx) {
  if (e->kind != ExprKind::kSelect || !e->base || !e->index ||
      e->base->kind != ExprKind::kIdentifier) {
    return;
  }
  auto it = ctx.var_array_info.find(e->base->text);
  if (it == ctx.var_array_info.end() || !it->second.is_assoc ||
      ctx.class_names.count(it->second.assoc_index_type) == 0) {
    return;
  }
  auto index_class = it->second.assoc_index_type;
  if (IsIllegalClassIndex(e->index, index_class, ctx)) {
    ctx.diag.Error(
        e->range.start,
        std::format("class-indexed associative array '{}' shall be "
                    "indexed by an object of class '{}' or a derived class",
                    e->base->text, index_class));
  }
}

static void CheckClassIndexSelectExpr(const Expr* e, const ClassIndexCtx& ctx) {
  if (!e) return;
  CheckClassIndexSelectNode(e, ctx);
  CheckClassIndexSelectExpr(e->lhs, ctx);
  CheckClassIndexSelectExpr(e->rhs, ctx);
  CheckClassIndexSelectExpr(e->base, ctx);
  CheckClassIndexSelectExpr(e->index, ctx);
  CheckClassIndexSelectExpr(e->condition, ctx);
  CheckClassIndexSelectExpr(e->true_expr, ctx);
  CheckClassIndexSelectExpr(e->false_expr, ctx);
  for (const auto* elem : e->elements) {
    CheckClassIndexSelectExpr(elem, ctx);
  }
}

// Checks every expression directly attached to a statement node against the
// class-index rule (excluding nested sub-statements).
static void CheckStmtExprsForClassIndexSelect(const Stmt* s,
                                              const ClassIndexCtx& ctx) {
  CheckClassIndexSelectExpr(s->lhs, ctx);
  CheckClassIndexSelectExpr(s->rhs, ctx);
  CheckClassIndexSelectExpr(s->expr, ctx);
  CheckClassIndexSelectExpr(s->condition, ctx);
}

static void WalkStmtsForClassIndexSelect(const Stmt* s,
                                         const ClassIndexCtx& ctx) {
  if (!s) return;
  CheckStmtExprsForClassIndexSelect(s, ctx);
  for (auto* sub : s->stmts) WalkStmtsForClassIndexSelect(sub, ctx);
  WalkStmtsForClassIndexSelect(s->then_branch, ctx);
  WalkStmtsForClassIndexSelect(s->else_branch, ctx);
  WalkStmtsForClassIndexSelect(s->body, ctx);
  WalkStmtsForClassIndexSelect(s->for_body, ctx);
  for (auto& ci : s->case_items) WalkStmtsForClassIndexSelect(ci.body, ctx);
}

// Collects the classes declared directly inside a module, keyed by name. These
// module-local classes are not reachable through unit->classes, so the §7.8.3
// derivation walk needs them gathered separately to resolve a base class.
static std::unordered_map<std::string_view, const ClassDecl*>
CollectModuleLocalClasses(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ClassDecl*> local_classes;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      local_classes[item->class_decl->name] = item->class_decl;
    }
  }
  return local_classes;
}

void Elaborator::ValidateClassIndexSelect(const ModuleDecl* decl) {
  bool has_class_index = false;
  for (const auto& entry : var_array_info_) {
    const auto& info = entry.second;
    if (info.is_assoc && class_names_.count(info.assoc_index_type) > 0) {
      has_class_index = true;
      break;
    }
  }
  if (!has_class_index) return;
  auto local_classes = CollectModuleLocalClasses(decl);
  ClassIndexCtx ctx{var_array_info_,
                    class_var_types_,
                    class_names_,
                    local_classes,
                    var_types_,
                    unit_,
                    diag_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckClassIndexSelectExpr(item->assign_lhs, ctx);
      CheckClassIndexSelectExpr(item->assign_rhs, ctx);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForClassIndexSelect(item->body, ctx);
    }
  }
}

// §7.8.2: an associative array declared with a string index may only be
// indexed by a string or a string literal of any length. Any other index
// expression type is a type check error. An empty string literal is a string
// literal and therefore valid.
//
// Returns true when the index of a string-indexed associative array select is
// an illegal index (a non-string literal, or an identifier of a non-string
// type). A string literal of any length, including "", is valid.
static bool IsIllegalStringIndex(const Expr* idx, const TypeMap& var_types) {
  if (idx->kind == ExprKind::kStringLiteral) {
    // A string literal of any length, including "", is a valid index.
    return false;
  }
  if (IsLiteralExpr(idx->kind)) {
    // Any other literal (integer, real, time, unbased-unsized) is a
    // different type.
    return true;
  }
  if (idx->kind == ExprKind::kIdentifier) {
    auto vt = var_types.find(idx->text);
    if (vt != var_types.end() && vt->second != DataTypeKind::kString) {
      return true;
    }
  }
  return false;
}

// Validates a single select node against the string-index rule, emitting a
// diagnostic when its index expression is illegal. Non-select nodes and slice
// selects are ignored.
static void CheckStringIndexSelectNode(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const TypeMap& var_types, DiagEngine& diag) {
  // Plain element selects only; a slice on an associative array is reported
  // separately, so skip it here to avoid a second diagnostic on one site.
  if (e->kind != ExprKind::kSelect || !e->base || !e->index ||
      e->base->kind != ExprKind::kIdentifier || IsSliceSelect(e)) {
    return;
  }
  auto it = var_array_info.find(e->base->text);
  if (it == var_array_info.end() || !it->second.is_assoc ||
      it->second.assoc_index_type != "string") {
    return;
  }
  if (IsIllegalStringIndex(e->index, var_types)) {
    diag.Error(e->range.start,
               std::format("string-indexed associative array '{}' shall be "
                           "indexed by a string or string literal",
                           e->base->text));
  }
}

static void CheckStringIndexSelectExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  CheckStringIndexSelectNode(e, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->lhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->rhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->base, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->index, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->condition, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->true_expr, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->false_expr, var_array_info, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckStringIndexSelectExpr(elem, var_array_info, var_types, diag);
  }
}

static void WalkStmtsForStringIndexSelect(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckStringIndexSelectExpr(s->lhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->rhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->expr, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->condition, var_array_info, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForStringIndexSelect(sub, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->then_branch, var_array_info, var_types,
                                diag);
  WalkStmtsForStringIndexSelect(s->else_branch, var_array_info, var_types,
                                diag);
  WalkStmtsForStringIndexSelect(s->body, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->for_body, var_array_info, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForStringIndexSelect(ci.body, var_array_info, var_types, diag);
}

void Elaborator::ValidateStringIndexSelect(const ModuleDecl* decl) {
  bool has_string_index = false;
  for (const auto& entry : var_array_info_) {
    const auto& info = entry.second;
    if (info.is_assoc && info.assoc_index_type == "string") {
      has_string_index = true;
      break;
    }
  }
  if (!has_string_index) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringIndexSelectExpr(item->assign_lhs, var_array_info_, var_types_,
                                 diag_);
      CheckStringIndexSelectExpr(item->assign_rhs, var_array_info_, var_types_,
                                 diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForStringIndexSelect(item->body, var_array_info_, var_types_,
                                    diag_);
    }
  }
}

// §7.8.4: indexing an integral-index associative array casts the index
// expression to the index type, but an implicit cast from a real or shortreal
// expression is illegal. Flag any element select on such an array whose index
// is a nonintegral (real) expression.
static void CheckIntegralIndexSelectExpr(
    const Expr* e, const std::unordered_set<std::string_view>& integral_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base && e->index &&
      e->base->kind == ExprKind::kIdentifier && !IsSliceSelect(e) &&
      integral_names.count(e->base->text) &&
      IsNonintegralIndex(e->index, var_types)) {
    diag.Error(e->index->range.start,
               std::format("real or shortreal index is not allowed on "
                           "integral-indexed associative array '{}'",
                           e->base->text));
  }
  CheckIntegralIndexSelectExpr(e->lhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->rhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->base, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->index, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->condition, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->true_expr, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->false_expr, integral_names, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckIntegralIndexSelectExpr(elem, integral_names, var_types, diag);
  }
}

static void WalkStmtsForIntegralIndexSelect(
    const Stmt* s, const std::unordered_set<std::string_view>& integral_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckIntegralIndexSelectExpr(s->lhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->rhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->expr, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->condition, integral_names, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForIntegralIndexSelect(sub, integral_names, var_types, diag);
  WalkStmtsForIntegralIndexSelect(s->then_branch, integral_names, var_types,
                                  diag);
  WalkStmtsForIntegralIndexSelect(s->else_branch, integral_names, var_types,
                                  diag);
  WalkStmtsForIntegralIndexSelect(s->body, integral_names, var_types, diag);
  WalkStmtsForIntegralIndexSelect(s->for_body, integral_names, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForIntegralIndexSelect(ci.body, integral_names, var_types, diag);
}

// Returns true when an associative-array index type spelled `t` denotes an
// integral type: a builtin integral keyword, or a typedef resolving to one.
static bool IsIntegralIndexType(std::string_view t,
                                const TypedefMap& typedefs) {
  bool is_builtin = t == "int" || t == "integer" || t == "byte" ||
                    t == "shortint" || t == "longint";
  if (is_builtin) return true;
  auto it = typedefs.find(t);
  return it != typedefs.end() && IsIntegralType(it->second.kind);
}

// Collects the names of every associative array whose index type is integral
// (and is neither string-, wildcard-, nor class-indexed).
static std::unordered_set<std::string_view> CollectIntegralIndexNames(
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs) {
  std::unordered_set<std::string_view> integral_names;
  for (const auto& [name, info] : var_array_info) {
    if (!info.is_assoc) continue;
    auto t = info.assoc_index_type;
    if (t == "string" || t == "*" || class_names.count(t)) continue;
    if (IsIntegralIndexType(t, typedefs)) integral_names.insert(name);
  }
  return integral_names;
}

void Elaborator::ValidateIntegralIndexSelect(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> integral_names =
      CollectIntegralIndexNames(var_array_info_, class_names_, typedefs_);
  if (integral_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckIntegralIndexSelectExpr(item->assign_lhs, integral_names, var_types_,
                                   diag_);
      CheckIntegralIndexSelectExpr(item->assign_rhs, integral_names, var_types_,
                                   diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForIntegralIndexSelect(item->body, integral_names, var_types_,
                                      diag_);
    }
  }
}

static bool ContainsRealType(const DataType& dtype, const TypedefMap& tds,
                             int depth = 0) {
  // Guard against a pathological recursive typedef chain; a legitimate type
  // nests only a handful of levels deep.
  if (depth > 16) return false;
  if (dtype.kind == DataTypeKind::kNamed) {
    auto it = tds.find(dtype.type_name);
    if (it != tds.end()) return ContainsRealType(it->second, tds, depth + 1);
    return false;
  }
  if (IsRealType(dtype.kind)) return true;
  for (const auto& m : dtype.struct_members) {
    if (IsRealType(m.type_kind)) return true;
    // A member written through a typedef only reveals a real after the alias is
    // resolved, so follow a named member type into the typedef table and check
    // whatever it ultimately denotes (including a nested struct that holds
    // one).
    if (m.type_kind == DataTypeKind::kNamed) {
      auto it = tds.find(m.type_name);
      if (it != tds.end() && ContainsRealType(it->second, tds, depth + 1))
        return true;
    }
  }
  return false;
}

void Elaborator::ValidateAssocIndexType(const ModuleItem* item) {
  if (item->unpacked_dims.empty()) return;
  auto* dim = item->unpacked_dims[0];
  if (!dim || dim->kind != ExprKind::kIdentifier) return;
  auto t = dim->text;
  if (t == "real" || t == "shortreal" || t == "realtime") {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
    return;
  }

  auto it = typedefs_.find(t);
  if (it != typedefs_.end() && ContainsRealType(it->second, typedefs_)) {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
  }
}

}  // namespace delta
