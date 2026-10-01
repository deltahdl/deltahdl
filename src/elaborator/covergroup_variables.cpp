#include "elaborator/covergroup_variables.h"

#include <string_view>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

Expr* MakeIdentifier(std::string_view text, SourceLoc loc, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = text;
  id->range.start = loc;
  return id;
}

}  // namespace

const CovergroupDecl* DeclaredCovergroup(const DataType& dt,
                                         const RtlirModule* mod) {
  if (dt.kind != DataTypeKind::kNamed) return nullptr;
  for (const ModuleItem* item : mod->let_decls) {
    if (item->kind == ModuleItemKind::kCovergroupDecl &&
        item->name == dt.type_name) {
      return item->covergroup;
    }
  }
  return nullptr;
}

void AddCovergroupEventProcess(std::string_view var_name,
                               const CovergroupDecl& cg, SourceLoc loc,
                               RtlirModule* mod, Arena& arena) {
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeIdentifier(var_name, loc, arena);
  access->rhs = MakeIdentifier("sample", loc, arena);
  access->range.start = loc;
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = access;
  call->range.start = loc;
  auto* sample = arena.Create<Stmt>();
  sample->kind = StmtKind::kExprStmt;
  sample->expr = call;
  sample->range.start = loc;
  auto* wait = arena.Create<Stmt>();
  wait->kind = StmtKind::kEventControl;
  wait->events = cg.event.clocking;
  wait->body = sample;
  wait->range.start = loc;
  RtlirProcess process;
  process.kind = RtlirProcessKind::kAlways;
  process.loc = loc;
  process.body = wait;
  mod->processes.push_back(process);
}

}  // namespace delta
