#include "elaborator/class_property_cont_assign.h"

#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

struct PropertyWriteScan {
  const std::unordered_map<std::string_view, std::string_view>& handle_types;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

}  // namespace

// The `h.x` a target is rooted at, its selects and the members selected out
// of the property taken off; null for a target that is not a member reached
// through a plain name.
static const Expr* HandleMemberRoot(const Expr* e) {
  for (;;) {
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
    } else if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
      return nullptr;
    } else if (e->lhs->kind == ExprKind::kIdentifier) {
      return e;
    } else {
      e = e->lhs;
    }
  }
}

static void CheckTarget(const Expr* target, SourceLoc loc,
                        const PropertyWriteScan& scan) {
  if (target->kind == ExprKind::kConcatenation) {
    for (const Expr* element : target->elements) {
      CheckTarget(element, loc, scan);
    }
    return;
  }
  const Expr* access = HandleMemberRoot(target);
  if (access == nullptr) return;
  auto handle = scan.handle_types.find(access->lhs->text);
  if (handle == scan.handle_types.end()) return;
  const ClassMember* property = FindMemberInClass(
      FindClassDecl(handle->second, scan.unit), access->rhs->text, scan.unit);
  if (property == nullptr || property->is_static) return;
  scan.diag.Error(loc,
                  std::format("'{}.{}' is a non-static class property, which "
                              "no continuous or procedural continuous "
                              "assignment may write",
                              access->lhs->text, access->rhs->text),
                  Subclause("6.21"));
}

static void CheckStmt(const Stmt* s, const PropertyWriteScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce) {
    CheckTarget(s->lhs, s->range.start, scan);
  }
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

void CheckContinuousPropertyWrites(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, std::string_view>& handle_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const PropertyWriteScan kScan{handle_types, unit, diag};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTarget(item->assign_lhs, item->loc, kScan);
    }
    CheckStmt(item->body, kScan);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kScan);
  }
}

}  // namespace delta
