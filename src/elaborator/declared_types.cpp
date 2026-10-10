#include "elaborator/declared_types.h"

#include <vector>

#include "elaborator/aggregate_shape.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static void VisitStmt(const Stmt* s, const DeclaredTypeVisit& visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    visit({s->var_decl_type, s->var_unpacked_dims, s->range.start});
  }
  ForEachChildStmt(s, [&visit](Stmt* const& sub) { VisitStmt(sub, visit); });
}

// A function's return carries no unpacked dimension of its own.
static const std::vector<Expr*>& NoDims() {
  static const std::vector<Expr*> kNone;
  return kNone;
}

static void VisitSubroutine(const ModuleItem* item,
                            const DeclaredTypeVisit& visit) {
  visit({item->return_type, NoDims(), item->loc});
  for (const FunctionArg& arg : item->func_args) {
    visit({arg.data_type, arg.unpacked_dims, item->loc});
  }
  for (const Stmt* s : item->func_body_stmts) VisitStmt(s, visit);
}

static void VisitClass(const ClassDecl* cls, const DeclaredTypeVisit& visit);

// What an item declares within itself: a procedural block's or a
// subroutine's declarations, and a class's members.
static void VisitInner(const ModuleItem* item, const DeclaredTypeVisit& visit) {
  if (item->class_decl != nullptr) VisitClass(item->class_decl, visit);
  if (item->kind == ModuleItemKind::kFunctionDecl ||
      item->kind == ModuleItemKind::kTaskDecl) {
    VisitSubroutine(item, visit);
  }
  VisitStmt(item->body, visit);
}

static void VisitTypedef(const ModuleItem* item,
                         const DeclaredTypeVisit& visit) {
  visit({item->typedef_type, item->unpacked_dims, item->loc});
}

static void VisitVariable(const ModuleItem* item,
                          const DeclaredTypeVisit& visit) {
  visit({item->data_type, item->unpacked_dims, item->loc});
}

static void VisitClass(const ClassDecl* cls, const DeclaredTypeVisit& visit) {
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty) {
      visit({m->data_type, m->unpacked_dims, m->loc});
    }
    if (m->method != nullptr) VisitInner(m->method, visit);
    if (m->typedef_item != nullptr) VisitTypedef(m->typedef_item, visit);
    if (m->nested_class != nullptr) VisitClass(m->nested_class, visit);
  }
}

void ForEachInnerDeclaredType(const ModuleDecl* decl,
                              const DeclaredTypeVisit& visit) {
  for (const PortDecl& port : decl->ports) {
    visit({port.data_type, port.unpacked_dims, port.loc});
  }
  for (const ModuleItem* item : decl->items) VisitInner(item, visit);
}

void ForEachUnitDeclaredType(const CompilationUnit* unit,
                             const DeclaredTypeVisit& visit) {
  for (const ModuleItem* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kVarDecl) VisitVariable(item, visit);
    VisitInner(item, visit);
  }
  for (const ClassDecl* cls : unit->classes) VisitClass(cls, visit);
  for (const PackageDecl* pkg : unit->packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind == ModuleItemKind::kVarDecl) VisitVariable(item, visit);
      if (item->kind == ModuleItemKind::kTypedef) VisitTypedef(item, visit);
      VisitInner(item, visit);
    }
  }
}

void CheckDeclaredTypeRules(const DeclaredType& declared,
                            const AggregateShapeCtx& ctx) {
  CheckAggregateShape(declared.type, declared.loc, ctx);
  CheckRealAssocIndexTypes(declared.unpacked_dims, declared.loc,
                           ctx.tables.typedefs, ctx.diag);
}

}  // namespace delta
