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

// Reports `ref`, a `$unit::` name, unless a declaration of the unit written
// before it, or a task or function of the unit written anywhere, is what it
// names.
void CheckUnitScopedName(const Expr* ref, const CompilationUnit* unit,
                         DiagEngine& diag) {
  bool declared_after = false;
  auto names_it = [&](std::string_view name, SourceLoc loc, bool any_order) {
    if (name != ref->text) return false;
    if (any_order || PrecedesInText(loc, ref->range.start)) return true;
    declared_after = true;
    return false;
  };
  for (const auto* item : unit->cu_items) {
    bool is_subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                         item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kDpiImport;
    if (names_it(item->name, item->loc, is_subroutine)) return;
    if (DeclaresEnumMember(item, ref->text) &&
        names_it(ref->text, item->loc, false))
      return;
  }
  for (const auto* cls : unit->classes) {
    if (names_it(cls->name, cls->range.start, false)) return;
  }
  for (const auto* chk : unit->checkers) {
    if (names_it(chk->name, chk->range.start, false)) return;
  }
  if (declared_after) {
    diag.Error(ref->range.start,
               std::format("'$unit::{}' precedes its declaration in the "
                           "compilation unit",
                           ref->text),
               Subclause("3.12.1"));
    return;
  }
  diag.Error(ref->range.start,
             std::format("undeclared identifier '$unit::{}'", ref->text),
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
