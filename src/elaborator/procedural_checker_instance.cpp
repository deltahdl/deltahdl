#include "elaborator/procedural_checker_instance.h"

#include <format>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// §17.3: a checker shall not be instantiated in a fork-join, fork-join_any
// or fork-join_none block, so one a fork statement encloses, `in_fork`, is
// reported and left out.
void CollectCheckerInstantiations(Stmt* s, bool in_fork,
                                  std::vector<Stmt*>& out, DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kCheckerInstantiation && in_fork) {
    diag.Error(s->range.start,
               "a checker shall not be instantiated in a fork-join, "
               "fork-join_any or fork-join_none block",
               Subclause("17.3"));
  } else if (s->kind == StmtKind::kCheckerInstantiation) {
    out.push_back(s);
  }
  bool sub_in_fork = in_fork || s->kind == StmtKind::kFork;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectCheckerInstantiations(sub, sub_in_fork, out, diag);
  });
}

}  // namespace

std::vector<Stmt*> CheckerInstantiationsIn(Stmt* body, DiagEngine& diag) {
  std::vector<Stmt*> out;
  CollectCheckerInstantiations(body, false, out, diag);
  return out;
}

bool AdmitProceduralCheckerInstance(const ModuleItem* item,
                                    const ModuleDecl* child,
                                    const RtlirModule* mod, DiagEngine& diag) {
  if (child == nullptr) return true;
  if (child->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("'{}' is not a checker, and only a checker may be "
                           "instantiated in procedural code",
                           item->inst_module),
               Subclause("17.3"));
    return false;
  }
  if (mod->is_checker) {
    diag.Error(item->loc,
               std::format("checker '{}' shall not be instantiated in a "
                           "procedure of another checker",
                           item->inst_module),
               Subclause("17.3"));
    return false;
  }
  CheckCheckerInstForm(item, child, diag);
  return true;
}

}  // namespace delta
