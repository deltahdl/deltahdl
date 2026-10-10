#include "elaborator/unit_scope_order.h"

#include <format>
#include <string_view>
#include <tuple>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

bool PrecedesInText(SourceLoc a, SourceLoc b) {
  return std::tie(a.file_id, a.line, a.column) <
         std::tie(b.file_id, b.line, b.column);
}

static bool IsDataItem(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kVarDecl ||
         item->kind == ModuleItemKind::kNetDecl;
}

bool UnitDeclaresData(const CompilationUnit* unit, std::string_view name,
                      SourceLoc reference) {
  for (const auto* item : unit->cu_items) {
    if (IsDataItem(item) && item->name == name &&
        PrecedesInText(item->loc, reference)) {
      return true;
    }
  }
  return false;
}

bool UnitDataDeclaredOnlyAfter(const CompilationUnit* unit,
                               std::string_view name, SourceLoc reference) {
  bool declared_after = false;
  for (const auto* item : unit->cu_items) {
    if (item->name != name) continue;
    if (PrecedesInText(item->loc, reference)) return false;
    if (IsDataItem(item)) declared_after = true;
  }
  return declared_after;
}

std::vector<ModuleItem*> UnitItemsBefore(const CompilationUnit* unit,
                                         SourceLoc reference) {
  std::vector<ModuleItem*> before;
  for (auto* item : unit->cu_items) {
    if (PrecedesInText(item->loc, reference)) before.push_back(item);
  }
  return before;
}

namespace {

void CollectUnitScopedInExpr(const Expr* e, std::vector<const Expr*>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier && e->scope_prefix == "$unit") {
    out.push_back(e);
  }
  ForEachExprChild(e,
                   [&](const Expr* sub) { CollectUnitScopedInExpr(sub, out); });
}

void CollectUnitScopedInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](const Expr* e) { CollectUnitScopedInExpr(e, out); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectUnitScopedInStmt(sub, out); });
}

// Whether `item` names `name` among the enumeration members it declares
// (§6.19), which are declarations of the scope the item stands in.
bool DeclaresEnumMember(const ModuleItem* item, std::string_view name) {
  bool found = false;
  ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
    for (const auto& member : type.enum_members) {
      if (member.name == name) found = true;
    }
  });
  return found;
}

// A search of the unit for the declaration `ref`, a `$unit::` name, names.
struct UnitNameSearch {
  const Expr* ref;
  // Set when a declaration of the name stands only after `ref`.
  bool declared_after = false;

  // Whether the declaration of `name` at `loc` is one `ref` names: a
  // declaration written before it, or one that `any_order` lets be written
  // anywhere.
  bool Names(std::string_view name, SourceLoc loc, bool any_order) {
    if (name != ref->text) return false;
    if (any_order || PrecedesInText(loc, ref->range.start)) return true;
    declared_after = true;
    return false;
  }
};

// Whether a declaration of the unit written before the search's reference, or
// a task or function of the unit written anywhere, is what it names. A class
// is reached as the head of `$unit::C::K`; a checker is no expression primary,
// so no `$unit::` identifier names one.
bool FindsUnitDeclaration(UnitNameSearch& search, const CompilationUnit* unit) {
  for (const auto* item : unit->cu_items) {
    bool is_subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                         item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kDpiImport;
    if (search.Names(item->name, item->loc, is_subroutine)) return true;
    if (DeclaresEnumMember(item, search.ref->text) &&
        search.Names(search.ref->text, item->loc, false))
      return true;
  }
  for (const auto* cls : unit->classes) {
    if (search.Names(cls->name, cls->range.start, false)) return true;
  }
  return false;
}

// Reports `ref`, a `$unit::` name, unless FindsUnitDeclaration finds what it
// names.
void CheckUnitScopedName(const Expr* ref, const CompilationUnit* unit,
                         DiagEngine& diag) {
  UnitNameSearch search{ref};
  if (FindsUnitDeclaration(search, unit)) return;
  diag.Error(ref->range.start,
             search.declared_after
                 ? std::format("'$unit::{}' precedes its declaration in the "
                               "compilation unit",
                               ref->text)
                 : std::format("undeclared identifier '$unit::{}'", ref->text),
             Subclause("3.12.1"));
}

}  // namespace

void ReportUnitScopedReferences(const std::vector<ModuleItem*>& items,
                                const CompilationUnit* unit, DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : items) {
    CollectUnitScopedInStmt(item->body, refs);
    for (const auto* s : item->func_body_stmts) {
      CollectUnitScopedInStmt(s, refs);
    }
    CollectUnitScopedInExpr(item->assign_lhs, refs);
    CollectUnitScopedInExpr(item->assign_rhs, refs);
    CollectUnitScopedInExpr(item->init_expr, refs);
  }
  for (const auto* ref : refs) CheckUnitScopedName(ref, unit, diag);
}

}  // namespace delta
