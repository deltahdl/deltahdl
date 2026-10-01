#include "elaborator/procedural_checker_instance.h"

#include <format>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

void CollectCheckerInstantiations(Stmt* s, std::vector<Stmt*>& out) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kCheckerInstantiation) out.push_back(s);
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectCheckerInstantiations(sub, out); });
}

}  // namespace

std::vector<Stmt*> CheckerInstantiationsIn(Stmt* body) {
  std::vector<Stmt*> out;
  CollectCheckerInstantiations(body, out);
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
