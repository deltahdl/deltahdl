#include <algorithm>
#include <format>
#include <iterator>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/value_kind.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct ArrayMethodScan {
  const ValueScope& values;
  DiagEngine& diag;
  const std::unordered_map<std::string_view, std::string_view>& class_vars;
  const CompilationUnit* unit;
};

bool IsArrayOrderingMethod(std::string_view name) {
  return name == "sort" || name == "rsort" || name == "reverse" ||
         name == "shuffle";
}

bool OrderingMethodRejectsWith(std::string_view name) {
  return name == "reverse" || name == "shuffle";
}

bool IsArrayReductionMethod(std::string_view name) {
  return name == "sum" || name == "product" || name == "and" || name == "or" ||
         name == "xor";
}

bool IsFindLocator(std::string_view name) {
  return name == "find" || name == "find_index" || name == "find_first" ||
         name == "find_first_index" || name == "find_last" ||
         name == "find_last_index";
}

bool ComparesElements(std::string_view name) {
  return name == "min" || name == "max" || name == "unique" ||
         name == "unique_index" || name == "sort" || name == "rsort";
}

bool IsManipulationMethod(std::string_view name) {
  return IsFindLocator(name) || ComparesElements(name) ||
         IsArrayOrderingMethod(name) || IsArrayReductionMethod(name) ||
         name == "map";
}

bool IsAssocMethod(std::string_view name) {
  return name == "delete" || name == "exists" || name == "first" ||
         name == "last" || name == "next" || name == "num" || name == "prev" ||
         name == "size";
}

bool IsQueueMethod(std::string_view name) {
  return name == "delete" || name == "insert" || name == "pop_back" ||
         name == "pop_front" || name == "push_back" || name == "push_front" ||
         name == "size";
}

bool IsDynamicMethod(std::string_view name) {
  return name == "delete" || name == "size";
}

bool IsKindMethod(const Elaborator::VarArrayInfo& info, std::string_view name) {
  if (info.is_assoc) return IsAssocMethod(name);
  if (info.is_queue) return IsQueueMethod(name);
  return info.is_dynamic && IsDynamicMethod(name);
}

struct ArrayKind {
  std::string_view words;
  std::string_view subclause;
};

ArrayKind KindOf(const Elaborator::VarArrayInfo& info) {
  if (info.is_assoc) return {"associative array", "7.9"};
  if (info.is_queue) return {"queue", "7.10.2"};
  if (info.is_dynamic) return {"dynamic array", "7.5"};
  return {"fixed-size array", "7.12"};
}

bool LacksReduction(std::string_view method, ValueKind kind) {
  if (kind == ValueKind::kOther || kind == ValueKind::kString) return true;
  bool bitwise = method == "and" || method == "or" || method == "xor";
  return bitwise && kind == ValueKind::kReal;
}

struct ArrayMethodSite {
  const Expr* base = nullptr;
  std::string_view method;
  const Expr* with_expr = nullptr;
  const Expr* iterator = nullptr;
};

bool MatchArrayMethodSite(const Expr* e, ArrayMethodSite& out) {
  const Expr* access = nullptr;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    access = e->lhs;
    if (!e->args.empty()) out.iterator = e->args.front();
  } else if (e->kind == ExprKind::kMemberAccess) {
    access = e;
  } else {
    return false;
  }
  if (!access->lhs || !access->rhs ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  out.base = access->lhs;
  out.method = access->rhs->text;
  out.with_expr = e->with_expr;
  return true;
}

ValueKind KindVisited(const ArrayMethodSite& site,
                      const Elaborator::VarArrayInfo& info,
                      const ArrayMethodScan& scan) {
  if (site.with_expr == nullptr) return KindOfElement(info, scan.values);
  ValueScope with_scope = scan.values;
  with_scope.iterator = {
      site.iterator != nullptr ? site.iterator->text : "item", &info};
  return KindOfValue(site.with_expr, with_scope);
}

bool ReportMissingWith(const Expr* e, const ArrayMethodSite& site,
                       DiagEngine& diag) {
  if (site.with_expr != nullptr) return false;
  if (site.iterator != nullptr) {
    diag.Error(site.iterator->range.start,
               "iterator argument without 'with' clause", Subclause("7.12"));
    return true;
  }
  if (IsFindLocator(site.method)) {
    diag.Error(e->range.start,
               std::format("array locator method '{}' requires a 'with' "
                           "clause",
                           site.method),
               Subclause("7.12.1"));
    return true;
  }
  if (site.method == "map") {
    diag.Error(e->range.start, "array method 'map' requires a 'with' clause",
               Subclause("7.12.5"));
    return true;
  }
  return false;
}

void ReportUnorderedComparison(const Expr* e, const ArrayMethodSite& site,
                               const Elaborator::VarArrayInfo& info,
                               const ArrayMethodScan& scan) {
  if (!ComparesElements(site.method)) return;
  if (KindVisited(site, info, scan) != ValueKind::kOther) return;
  scan.diag.Error(
      e->range.start,
      std::format("array method '{}' compares values of a type "
                  "without relational operators",
                  site.method),
      Subclause(IsArrayOrderingMethod(site.method) ? "7.12.2" : "7.12.1"));
}

void ReportReduction(const Expr* e, const ArrayMethodSite& site,
                     const Elaborator::VarArrayInfo& info,
                     const ArrayMethodScan& scan) {
  if (site.with_expr == nullptr && info.num_unpacked_dims >= 2) {
    scan.diag.Error(e->range.start,
                    std::format("array reduction method '{}' requires a "
                                "'with' clause over an array whose elements "
                                "are arrays",
                                site.method),
                    Subclause("7.12.3"));
    return;
  }
  if (!LacksReduction(site.method, KindVisited(site, info, scan))) return;
  scan.diag.Error(e->range.start,
                  std::format("array reduction method '{}' reduces values of "
                              "a type its operation is not defined for",
                              site.method),
                  Subclause("7.12.3"));
}

void ReportOrdering(const Expr* e, const ArrayMethodSite& site,
                    const Elaborator::VarArrayInfo& info, DiagEngine& diag) {
  if (info.is_assoc) {
    diag.Error(e->range.start,
               std::format("array ordering method '{}' cannot be applied to "
                           "associative array '{}'",
                           site.method, site.base->text),
               Subclause("7.12.2"));
    return;
  }
  if (site.with_expr != nullptr && OrderingMethodRejectsWith(site.method)) {
    diag.Error(e->range.start,
               std::format("array ordering method '{}' does not accept a "
                           "'with' clause",
                           site.method),
               Subclause("7.12.2"));
  }
}

void CheckArrayMethodSite(const Expr* e, const ArrayMethodSite& site,
                          const Elaborator::VarArrayInfo& info,
                          const ArrayMethodScan& scan) {
  if (!IsManipulationMethod(site.method)) {
    if (IsKindMethod(info, site.method)) return;
    ArrayKind kind = KindOf(info);
    scan.diag.Error(e->range.start,
                    std::format("'{}' is not a built-in method of the {} '{}'",
                                site.method, kind.words, site.base->text),
                    Subclause(kind.subclause));
    return;
  }
  if (ReportMissingWith(e, site, scan.diag)) return;
  if (IsArrayReductionMethod(site.method)) {
    ReportReduction(e, site, info, scan);
    return;
  }
  ReportUnorderedComparison(e, site, info, scan);
  if (IsArrayOrderingMethod(site.method)) {
    ReportOrdering(e, site, info, scan.diag);
  }
}

bool IsIndexTypeDim(const Expr& dim, const ValueScope& values) {
  static constexpr std::string_view kIndexTypes[] = {
      "string", "int",   "integer", "byte", "shortint", "longint",
      "bit",    "logic", "reg",     "time", "*"};
  if (dim.kind != ExprKind::kIdentifier) return false;
  return std::ranges::find(kIndexTypes, dim.text) != std::end(kIndexTypes) ||
         values.typedefs.contains(dim.text) ||
         values.class_names.contains(dim.text);
}

bool NamesClassType(const Expr& dim, const ClassDecl* cls,
                    const CompilationUnit* unit) {
  if (dim.kind != ExprKind::kIdentifier) return false;
  for (const auto* walk = cls; walk; walk = FindBaseClass(walk, unit)) {
    if (walk->type_param_names.contains(dim.text)) return true;
    for (const auto* m : walk->members) {
      if (m->kind == ClassMemberKind::kTypedef && m->name == dim.text)
        return true;
    }
  }
  return false;
}

struct DeclaredMember {
  const std::vector<Expr*>* dims = nullptr;
  bool random = false;
  const ClassDecl* owner = nullptr;
};

DeclaredMember MemberDeclared(const Expr& base, const ArrayMethodScan& scan) {
  if (base.kind != ExprKind::kMemberAccess || base.is_scope_resolution ||
      base.lhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  if (const StructMember* m = SelectedStructMember(&base, scan.values)) {
    return {&m->unpacked_dims, false};
  }
  auto handle = scan.class_vars.find(base.lhs->text);
  if (handle == scan.class_vars.end()) return {};
  const OwnedMember kProperty = FindMemberAndOwner(
      FindClassDecl(handle->second, scan.unit), base.rhs->text, scan.unit);
  if (kProperty.member == nullptr) return {};
  return {&kProperty.member->unpacked_dims,
          kProperty.member->is_rand || kProperty.member->is_randc,
          kProperty.owner};
}

void CheckMemberArrayMethod(const Expr* e, const ArrayMethodSite& site,
                            const ArrayMethodScan& scan) {
  const DeclaredMember kMember = MemberDeclared(*site.base, scan);
  const std::vector<Expr*>* dims = kMember.dims;
  if (dims == nullptr || dims->empty() || IsManipulationMethod(site.method) ||
      (kMember.random && site.method == "rand_mode")) {
    return;
  }
  Elaborator::VarArrayInfo info;
  const Expr* dim = dims->front();
  info.is_dynamic = dim == nullptr;
  info.is_queue = dim != nullptr && IsQueueDim(dim);
  info.is_assoc =
      dim != nullptr && (IsIndexTypeDim(*dim, scan.values) ||
                         NamesClassType(*dim, kMember.owner, scan.unit));
  if (IsKindMethod(info, site.method)) return;
  const ArrayKind kKind = KindOf(info);
  scan.diag.Error(e->range.start,
                  std::format("'{}' is not a built-in method of the {} '{}.{}'",
                              site.method, kKind.words, site.base->lhs->text,
                              site.base->rhs->text),
                  Subclause(kKind.subclause));
}

void CheckArrayMethodExpr(const Expr* e, const ArrayMethodScan& scan) {
  if (!e) return;
  ArrayMethodSite site;
  bool matched = MatchArrayMethodSite(e, site);
  if (matched && site.base->kind == ExprKind::kIdentifier) {
    auto it = scan.values.arrays.find(site.base->text);
    if (it != scan.values.arrays.end())
      CheckArrayMethodSite(e, site, it->second, scan);
  } else if (matched) {
    CheckMemberArrayMethod(e, site, scan);
  }
  CheckArrayMethodExpr(
      matched && e->kind == ExprKind::kCall ? site.base : e->lhs, scan);
  CheckArrayMethodExpr(e->rhs, scan);
  CheckArrayMethodExpr(e->base, scan);
  CheckArrayMethodExpr(e->index, scan);
  CheckArrayMethodExpr(e->condition, scan);
  CheckArrayMethodExpr(e->true_expr, scan);
  CheckArrayMethodExpr(e->false_expr, scan);
  for (const auto* a : e->args) CheckArrayMethodExpr(a, scan);
  for (const auto* elem : e->elements) CheckArrayMethodExpr(elem, scan);
}

void WalkStmtsForArrayMethods(const Stmt* s, const ArrayMethodScan& scan) {
  if (!s) return;
  CheckArrayMethodExpr(s->expr, scan);
  CheckArrayMethodExpr(s->lhs, scan);
  CheckArrayMethodExpr(s->rhs, scan);
  CheckArrayMethodExpr(s->condition, scan);
  ForEachChildStmt(
      s, [&scan](Stmt* const& sub) { WalkStmtsForArrayMethods(sub, scan); });
}

}  // namespace

bool IsArrayBuiltinMethodName(std::string_view name) {
  return IsManipulationMethod(name) || IsAssocMethod(name) ||
         IsQueueMethod(name) || IsDynamicMethod(name);
}

void Elaborator::ValidateArrayOrderingMethods(const ModuleDecl* decl) {
  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  const ArrayMethodScan kScan{kValues, diag_, class_var_types_, unit_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckArrayMethodExpr(item->assign_lhs, kScan);
      CheckArrayMethodExpr(item->assign_rhs, kScan);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) WalkStmtsForArrayMethods(item->body, kScan);
  }
}

}  // namespace delta
