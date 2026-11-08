#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "elaborator/value_kind.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsLiteralExpr(ExprKind kind) {
  return kind == ExprKind::kIntegerLiteral || kind == ExprKind::kRealLiteral ||
         kind == ExprKind::kTimeLiteral || kind == ExprKind::kStringLiteral ||
         kind == ExprKind::kUnbasedUnsizedLiteral;
}

struct ClassIndexCtx {
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_map<std::string_view, const ClassDecl*>& local_classes;
  const ValueScope& values;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

static const ClassDecl* FindClassDeclScoped(std::string_view name,
                                            const ClassIndexCtx& ctx) {
  auto it = ctx.local_classes.find(name);
  if (it != ctx.local_classes.end()) return it->second;
  return FindClassDecl(name, ctx.unit);
}

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

static bool IsIllegalClassIndex(const Expr* idx, std::string_view index_class,
                                const ClassIndexCtx& ctx) {
  bool is_null = idx->kind == ExprKind::kIdentifier && idx->text == "null";
  if (is_null) return false;
  if (IsLiteralExpr(idx->kind)) return true;
  if (idx->kind == ExprKind::kIdentifier) {
    auto vt = ctx.class_var_types.find(idx->text);
    if (vt != ctx.class_var_types.end()) {
      return !IsClassDerivedFromScoped(vt->second, index_class, ctx);
    }
    auto gt = ctx.values.var_types.find(idx->text);
    return gt != ctx.values.var_types.end() &&
           gt->second != DataTypeKind::kNamed;
  }
  ValueKind kind = KindOfValue(idx, ctx.values);
  return kind == ValueKind::kIntegral || kind == ValueKind::kReal ||
         kind == ValueKind::kString;
}

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
                    e->base->text, index_class),
        Subclause("7.8.3"));
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
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForClassIndexSelect(sub, ctx); });
}

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
  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  ClassIndexCtx ctx{var_array_info_,
                    class_var_types_,
                    class_names_,
                    local_classes,
                    kValues,
                    unit_,
                    diag_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckClassIndexSelectExpr(item->assign_lhs, ctx);
      CheckClassIndexSelectExpr(item->assign_rhs, ctx);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForClassIndexSelect(item->body, ctx);
    }
  }
}

static bool IsIllegalStringIndex(const Expr* idx, const ValueScope& values) {
  if (idx->kind == ExprKind::kStringLiteral) {
    return false;
  }
  if (IsLiteralExpr(idx->kind)) {
    return true;
  }
  if (idx->kind == ExprKind::kIdentifier) {
    auto vt = values.var_types.find(idx->text);
    return vt != values.var_types.end() && vt->second != DataTypeKind::kString;
  }
  ValueKind kind = KindOfValue(idx, values);
  return kind == ValueKind::kIntegral || kind == ValueKind::kReal ||
         kind == ValueKind::kOther;
}

static void CheckStringIndexSelectNode(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const ValueScope& values, DiagEngine& diag) {
  if (e->kind != ExprKind::kSelect || !e->base || !e->index ||
      e->base->kind != ExprKind::kIdentifier || IsSliceSelect(e)) {
    return;
  }
  auto it = var_array_info.find(e->base->text);
  if (it == var_array_info.end() || !it->second.is_assoc ||
      it->second.assoc_index_type != "string") {
    return;
  }
  if (IsIllegalStringIndex(e->index, values)) {
    diag.Error(e->range.start,
               std::format("string-indexed associative array '{}' shall be "
                           "indexed by a string or string literal",
                           e->base->text),
               Subclause("7.8.2"));
  }
}

static void CheckStringIndexSelectExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const ValueScope& values, DiagEngine& diag) {
  if (!e) return;
  CheckStringIndexSelectNode(e, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->lhs, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->rhs, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->base, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->index, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->condition, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->true_expr, var_array_info, values, diag);
  CheckStringIndexSelectExpr(e->false_expr, var_array_info, values, diag);
  for (const auto* elem : e->elements) {
    CheckStringIndexSelectExpr(elem, var_array_info, values, diag);
  }
}

static void WalkStmtsForStringIndexSelect(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const ValueScope& values, DiagEngine& diag) {
  if (!s) return;
  CheckStringIndexSelectExpr(s->lhs, var_array_info, values, diag);
  CheckStringIndexSelectExpr(s->rhs, var_array_info, values, diag);
  CheckStringIndexSelectExpr(s->expr, var_array_info, values, diag);
  CheckStringIndexSelectExpr(s->condition, var_array_info, values, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForStringIndexSelect(sub, var_array_info, values, diag);
  });
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
  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringIndexSelectExpr(item->assign_lhs, var_array_info_, kValues,
                                 diag_);
      CheckStringIndexSelectExpr(item->assign_rhs, var_array_info_, kValues,
                                 diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForStringIndexSelect(item->body, var_array_info_, kValues,
                                    diag_);
    }
  }
}

static void CheckIntegralIndexSelectExpr(
    const Expr* e, const std::unordered_set<std::string_view>& integral_names,
    const ValueScope& values, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base && e->index &&
      e->base->kind == ExprKind::kIdentifier && !IsSliceSelect(e) &&
      integral_names.count(e->base->text) &&
      IsNonintegralIndex(e->index, values)) {
    diag.Error(e->index->range.start,
               std::format("real or shortreal index is not allowed on "
                           "integral-indexed associative array '{}'",
                           e->base->text),
               Subclause("7.8.4"));
  }
  CheckIntegralIndexSelectExpr(e->lhs, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->rhs, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->base, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->index, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->condition, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->true_expr, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(e->false_expr, integral_names, values, diag);
  for (const auto* elem : e->elements) {
    CheckIntegralIndexSelectExpr(elem, integral_names, values, diag);
  }
}

static void WalkStmtsForIntegralIndexSelect(
    const Stmt* s, const std::unordered_set<std::string_view>& integral_names,
    const ValueScope& values, DiagEngine& diag) {
  if (!s) return;
  CheckIntegralIndexSelectExpr(s->lhs, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(s->rhs, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(s->expr, integral_names, values, diag);
  CheckIntegralIndexSelectExpr(s->condition, integral_names, values, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForIntegralIndexSelect(sub, integral_names, values, diag);
  });
}

static bool IsIntegralIndexType(std::string_view t,
                                const TypedefMap& typedefs) {
  bool is_builtin = t == "int" || t == "integer" || t == "byte" ||
                    t == "shortint" || t == "longint";
  if (is_builtin) return true;
  auto it = typedefs.find(t);
  return it != typedefs.end() && IsIntegralType(it->second.kind);
}

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
  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckIntegralIndexSelectExpr(item->assign_lhs, integral_names, kValues,
                                   diag_);
      CheckIntegralIndexSelectExpr(item->assign_rhs, integral_names, kValues,
                                   diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForIntegralIndexSelect(item->body, integral_names, kValues,
                                      diag_);
    }
  }
}

}  // namespace delta
