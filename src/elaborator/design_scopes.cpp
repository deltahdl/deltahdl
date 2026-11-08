#include "elaborator/design_scopes.h"

#include <string>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

void CollectBlockScopes(const Stmt* s, const std::string& path,
                        bool label_is_statement_label,
                        std::vector<std::string>& out) {
  if (s == nullptr) return;
  std::string here = path;
  if (label_is_statement_label && !s->label.empty()) {
    here = path + "." + std::string(s->label);
    out.push_back(here);
  }
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CollectBlockScopes(sub, here, true, out); });
}

void CollectModuleScopes(const RtlirModule* mod, const std::string& path,
                         std::vector<std::string>& out) {
  out.push_back(path);
  for (const auto* item : mod->function_decls) {
    out.push_back(path + "." + std::string(item->name));
  }
  for (const auto& proc : mod->processes) {
    const bool kWrittenProcedure =
        !proc.is_static_assertion && !proc.is_concurrent_clocked;
    CollectBlockScopes(proc.body, path, kWrittenProcedure, out);
  }
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    CollectModuleScopes(child.resolved,
                        path + "." + std::string(child.inst_name), out);
  }
}

void CollectInstanceVariables(const RtlirModule* mod, const std::string& path,
                              const std::string& prefix,
                              std::vector<ScopeDeclaredVariables>& out) {
  ScopeDeclaredVariables here{path, prefix, {}};
  for (const auto& net : mod->nets) here.names.emplace_back(net.name);
  for (const auto& var : mod->variables) here.names.emplace_back(var.name);
  out.push_back(std::move(here));
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    std::string inst(child.inst_name);
    std::string child_path = path;
    child_path += ".";
    child_path += inst;
    std::string child_prefix = prefix;
    child_prefix += inst;
    child_prefix += ".";
    CollectInstanceVariables(child.resolved, child_path, child_prefix, out);
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

std::vector<ScopeDeclaredVariables> ModuleInstanceVariables(
    const RtlirDesign* design) {
  std::vector<ScopeDeclaredVariables> out;
  for (const auto* top : design->top_modules) {
    CollectInstanceVariables(top, std::string(top->name), "", out);
  }
  return out;
}

}  // namespace delta
