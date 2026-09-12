#include "elaborator/design_scopes.h"

#include <string>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

namespace {

// The named blocks of a statement, each under the path of the blocks it
// stands in: a labelled begin-end or fork is a scope of its own and the
// statements it holds are named through it.
void CollectBlockScopes(const Stmt* s, const std::string& path,
                        std::vector<std::string>& out) {
  if (s == nullptr) return;
  std::string here = path;
  if ((s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) &&
      !s->label.empty()) {
    here = path + "." + std::string(s->label);
    out.push_back(here);
  }
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CollectBlockScopes(sub, here, out); });
}

// The scopes of one module instance at `path`: the instance itself, the tasks
// and functions it declares, the named blocks of its procedures, and the
// instances it holds, each by its instance name under this path.
void CollectModuleScopes(const RtlirModule* mod, const std::string& path,
                         std::vector<std::string>& out) {
  out.push_back(path);
  for (const auto* item : mod->function_decls) {
    out.push_back(path + "." + std::string(item->name));
  }
  for (const auto& proc : mod->processes) {
    CollectBlockScopes(proc.body, path, out);
  }
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    CollectModuleScopes(child.resolved,
                        path + "." + std::string(child.inst_name), out);
  }
}

}  // namespace

std::vector<std::string> CompleteHierarchicalScopeNames(
    const RtlirDesign* design) {
  std::vector<std::string> out;
  for (const auto* top : design->top_modules) {
    CollectModuleScopes(top, std::string(top->name), out);
  }
  return out;
}

}  // namespace delta
