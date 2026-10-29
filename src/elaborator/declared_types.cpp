#include "elaborator/declared_types.h"

#include <functional>
#include <string_view>
#include <vector>

#include "elaborator/aggregate_shape.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// A typedef or a nettype, whichever `item` declares: the two are written alike
// (A.2.1.3), and a nettype's type answers to §6.6.7 besides.
static void VisitTypedef(const ModuleItem* item,
                         const DeclaredTypeVisit& visit) {
  const bool kIsNettype = item->kind == ModuleItemKind::kNettypeDecl;
  visit({item->typedef_type, item->unpacked_dims, item->loc,
         kIsNettype ? item : nullptr});
}

// A block's nettype is carried as a kBlockItemDecl statement over its item
// (Parser::ParseBlockVarDecls).
static void VisitStmt(const Stmt* s, const DeclaredTypeVisit& visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    visit({s->var_decl_type, s->var_unpacked_dims, s->range.start});
  }
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kNettypeDecl) {
    VisitTypedef(s->decl_item, visit);
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
    if (item->kind == ModuleItemKind::kNettypeDecl) VisitTypedef(item, visit);
    VisitInner(item, visit);
  }
  for (const ClassDecl* cls : unit->classes) VisitClass(cls, visit);
  for (const PackageDecl* pkg : unit->packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind == ModuleItemKind::kVarDecl) VisitVariable(item, visit);
      if (item->kind == ModuleItemKind::kTypedef ||
          item->kind == ModuleItemKind::kNettypeDecl)
        VisitTypedef(item, visit);
      VisitInner(item, visit);
    }
  }
}

void CheckDeclaredTypeRules(
    const DeclaredType& declared, const AggregateShapeCtx& ctx,
    const std::function<bool(std::string_view)>& names_covergroup) {
  CheckAggregateShape(declared.type, declared.loc, ctx);
  CheckRealAssocIndexTypes(declared.unpacked_dims, declared.loc,
                           ctx.tables.typedefs, ctx.diag);
  if (declared.nettype != nullptr) {
    ReportIllegalNettypeDataType(*declared.nettype, ctx.tables, ctx.diag,
                                 names_covergroup);
  }
}

}  // namespace delta
