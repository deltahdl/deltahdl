#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/value_kind.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// What the array method checks read besides the call: the declarations that
// type what a method visits, the module's arrays among them, and where the
// reports go.
struct ArrayMethodScan {
  const ValueScope& values;
  DiagEngine& diag;
};

// §7.12.2: the array ordering methods. reverse() and shuffle() take no with
// clause, whereas sort() and rsort() accept an optional one.
bool IsArrayOrderingMethod(std::string_view name) {
  return name == "sort" || name == "rsort" || name == "reverse" ||
         name == "shuffle";
}

bool OrderingMethodRejectsWith(std::string_view name) {
  return name == "reverse" || name == "shuffle";
}

// §7.12.3: the array reduction methods.
bool IsArrayReductionMethod(std::string_view name) {
  return name == "sum" || name == "product" || name == "and" || name == "or" ||
         name == "xor";
}

// §7.12.1: the locators whose with clause is mandatory.
bool IsFindLocator(std::string_view name) {
  return name == "find" || name == "find_index" || name == "find_first" ||
         name == "find_first_index" || name == "find_last" ||
         name == "find_last_index";
}

// §7.12.1 and §7.12.2: the methods that, without a with clause, compare the
// elements themselves by their relational operators.
bool ComparesElements(std::string_view name) {
  return name == "min" || name == "max" || name == "unique" ||
         name == "unique_index" || name == "sort" || name == "rsort";
}

// §7.12: the manipulation methods every unpacked array has.
bool IsManipulationMethod(std::string_view name) {
  return IsFindLocator(name) || ComparesElements(name) ||
         IsArrayOrderingMethod(name) || IsArrayReductionMethod(name) ||
         name == "map";
}

// §7.5, §7.9 and §7.10.2: the methods a dynamic array, an associative array or
// a queue has besides those of §7.12. A fixed-size array has none.
bool IsKindMethod(const Elaborator::VarArrayInfo& info, std::string_view name) {
  if (info.is_assoc) {
    return name == "delete" || name == "exists" || name == "first" ||
           name == "last" || name == "next" || name == "num" ||
           name == "prev" || name == "size";
  }
  if (info.is_queue) {
    return name == "delete" || name == "insert" || name == "pop_back" ||
           name == "pop_front" || name == "push_back" || name == "push_front" ||
           name == "size";
  }
  return info.is_dynamic && (name == "delete" || name == "size");
}

// The words naming an array's kind and the subclause listing its methods.
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

// §7.12.3: sum and product need the arithmetic operators, which a string has
// not; and, or and xor the bitwise ones, which a real has not either. A value
// of a kind not known is not judged.
bool LacksReduction(std::string_view method, ValueKind kind) {
  if (kind == ValueKind::kOther || kind == ValueKind::kString) return true;
  bool bitwise = method == "and" || method == "or" || method == "xor";
  return bitwise && kind == ValueKind::kReal;
}

// Recognize an array-method invocation, in either the call form `arr.m()` or
// the property form `arr.m`. On success, `base` is the receiver expression,
// `method` is the method name, `with_expr` the with clause attached (the
// parser hangs it on the outermost expression in both forms), and `iterator`
// the iterator argument of the call form, or null.
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

// §7.12.1 to §7.12.3: what a method's operation is applied to: the with
// expression's value where the method is given one, and the element otherwise.
// The with expression names each element as it is visited, by the iterator
// argument or else as `item`.
ValueKind KindVisited(const ArrayMethodSite& site,
                      const Elaborator::VarArrayInfo& info,
                      const ArrayMethodScan& scan) {
  if (site.with_expr == nullptr) return KindOfElement(info, scan.values);
  ValueScope with_scope = scan.values;
  with_scope.iterator = {
      site.iterator != nullptr ? site.iterator->text : "item", &info};
  return KindOfValue(site.with_expr, with_scope);
}

// §7.12, §7.12.1 and §7.12.5: an iterator argument needs a with clause, and so
// do the find locators and map.
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

// §7.12.1 and §7.12.2: a method that compares what it visits needs relational
// operators on the element, or on the with expression where one is given.
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

// §7.12.3: a reduction leaves its with clause off only where the reduction is
// defined for the element type, which it is not for an element that is itself
// an unpacked array, as each element of an array of more than one unpacked
// dimension is; and the element, or the with expression's value, needs the
// reduction's operation.
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

// §7.12.2: ordering methods reorder any fixed or dynamically sized unpacked
// array but are not defined on associative arrays, and reverse()/shuffle()
// reject a with clause.
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

// The errors the method call `e`, of `site` on the array `info` describes,
// owes: a name that is no method of the array's kind, and the rules of §7.12
// on the with clause and on the operations the elements need.
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

void CheckArrayMethodExpr(const Expr* e, const ArrayMethodScan& scan) {
  if (!e) return;
  ArrayMethodSite site;
  bool matched = MatchArrayMethodSite(e, site);
  if (matched && site.base->kind == ExprKind::kIdentifier) {
    auto it = scan.values.arrays.find(site.base->text);
    if (it != scan.values.arrays.end())
      CheckArrayMethodSite(e, site, it->second, scan);
  }
  // The method access under a call is the site itself, already checked, so
  // only its receiver is walked below it.
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
  // §7.12 names no statement its rules are suspended in, so this descends
  // every link ForEachChildStmt in elaborator_validate_internal.h names and
  // names no link itself: `fork aa.sort(); join` and `assert (1) aa.sort();`
  // are judged as the same call one level up is.
  ForEachChildStmt(
      s, [&scan](Stmt* const& sub) { WalkStmtsForArrayMethods(sub, scan); });
}

}  // namespace

void Elaborator::ValidateArrayOrderingMethods(const ModuleDecl* decl) {
  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  const ArrayMethodScan kScan{kValues, diag_};
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
