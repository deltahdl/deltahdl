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

// What the array method checks read besides the call: the declarations that
// type what a method visits, the module's arrays among them, and where the
// reports go.
struct ArrayMethodScan {
  const ValueScope& values;
  DiagEngine& diag;
  // The class each class variable of the module holds a handle of, and the
  // unit those classes are found in, for an array reached through a handle.
  const std::unordered_map<std::string_view, std::string_view>& class_vars;
  const CompilationUnit* unit;
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

// §7.9: the methods an associative array has besides those of §7.12.
bool IsAssocMethod(std::string_view name) {
  return name == "delete" || name == "exists" || name == "first" ||
         name == "last" || name == "next" || name == "num" || name == "prev" ||
         name == "size";
}

// §7.10.2: the methods a queue has besides those of §7.12.
bool IsQueueMethod(std::string_view name) {
  return name == "delete" || name == "insert" || name == "pop_back" ||
         name == "pop_front" || name == "push_back" || name == "push_front" ||
         name == "size";
}

// §7.5: the methods a dynamic array has besides those of §7.12.
bool IsDynamicMethod(std::string_view name) {
  return name == "delete" || name == "size";
}

// §7.5, §7.9 and §7.10.2: the methods a dynamic array, an associative array or
// a queue has besides those of §7.12. A fixed-size array has none.
bool IsKindMethod(const Elaborator::VarArrayInfo& info, std::string_view name) {
  if (info.is_assoc) return IsAssocMethod(name);
  if (info.is_queue) return IsQueueMethod(name);
  return info.is_dynamic && IsDynamicMethod(name);
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

// §7.8: whether the unpacked dimension `dim` is an index type, which makes the
// declaration an associative array: a keyword index type, the `*` wildcard,
// or a name the scope's typedefs or classes declare.
bool IsIndexTypeDim(const Expr& dim, const ValueScope& values) {
  static constexpr std::string_view kIndexTypes[] = {
      "string", "int",   "integer", "byte", "shortint", "longint",
      "bit",    "logic", "reg",     "time", "*"};
  if (dim.kind != ExprKind::kIdentifier) return false;
  return std::ranges::find(kIndexTypes, dim.text) != std::end(kIndexTypes) ||
         values.typedefs.contains(dim.text) ||
         values.class_names.contains(dim.text);
}

// What the member `base` selects is declared with: its unpacked dimensions,
// and whether it is a random variable of an object, a property declared rand
// or randc, which gives it §18.8's rand_mode whatever its type.
struct DeclaredMember {
  const std::vector<Expr*>* dims = nullptr;
  bool random = false;
};

// That of a member of a structure variable, s.q, or of a property of the class
// a variable holds a handle of, h.q; no dimensions where `base` is neither. A
// structure variable is no object, so its member is no random variable even
// when declared rand.
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
  const ClassMember* property = FindMemberInClass(
      FindClassDecl(handle->second, scan.unit), base.rhs->text, scan.unit);
  if (property == nullptr) return {};
  return {&property->unpacked_dims, property->is_rand || property->is_randc};
}

// §7.5, §7.9, §7.10.2 and §7.12: the same rule for an array reached through a
// member, whose kind its first unpacked dimension makes as a variable's does.
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
  info.is_assoc = dim != nullptr && IsIndexTypeDim(*dim, scan.values);
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
