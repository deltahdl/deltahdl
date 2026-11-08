#include "elaborator/covergroup_variables.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
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

const CovergroupDecl* CovergroupNamed(const std::vector<ModuleItem*>& items,
                                      std::string_view name) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl && item->name == name) {
      return item->covergroup;
    }
  }
  return nullptr;
}

const CovergroupDecl* PackageCovergroup(const CompilationUnit* unit,
                                        std::string_view pkg_name,
                                        std::string_view name) {
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name == pkg_name) return CovergroupNamed(pkg->items, name);
  }
  return nullptr;
}

const CovergroupDecl* DeclaredCovergroup(const DataType& dt,
                                         const RtlirModule* mod,
                                         const CompilationUnit* unit) {
  if (dt.kind != DataTypeKind::kNamed) return nullptr;
  if (!dt.scope_name.empty()) {
    return PackageCovergroup(unit, dt.scope_name, dt.type_name);
  }
  return VisibleCovergroup(dt.type_name, mod, unit);
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
  call->is_coverage_event_sample = true;
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

}  // namespace

const CovergroupDecl* VisibleCovergroup(std::string_view name,
                                        const RtlirModule* mod,
                                        const CompilationUnit* unit) {
  if (const CovergroupDecl* own = CovergroupNamed(mod->let_decls, name)) {
    return own;
  }
  for (const RtlirImport& imp : mod->imports) {
    if (!imp.is_wildcard && imp.item_name != name) continue;
    if (const CovergroupDecl* imported =
            PackageCovergroup(unit, imp.package_name, name)) {
      return imported;
    }
  }
  return CovergroupNamed(unit->cu_items, name);
}

bool UnitDeclaresCovergroup(const CompilationUnit* unit,
                            std::string_view name) {
  if (CovergroupNamed(unit->cu_items, name) != nullptr) return true;
  return std::ranges::any_of(unit->packages, [&](const PackageDecl* pkg) {
    return CovergroupNamed(pkg->items, name) != nullptr;
  });
}

void BindCovergroupVariable(const ModuleItem& item, RtlirVariable& var,
                            RtlirModule* mod, const CompilationUnit* unit,
                            Arena& arena) {
  var.covergroup = DeclaredCovergroup(item.data_type, mod, unit);
  if (var.covergroup != nullptr &&
      var.covergroup->event.kind == CoverageEventKind::kClocking) {
    AddCovergroupEventProcess(item.name, *var.covergroup, item.loc, mod, arena);
  }
}

}  // namespace delta
