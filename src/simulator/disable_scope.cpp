#include "simulator/disable_scope.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_function_hier.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

struct StandingScopes {
  std::string base;
  std::vector<std::string_view> labels;
  std::vector<std::string> keys;
};

StandingScopes ScopesOf(const Process& proc, SimContext& ctx) {
  StandingScopes scopes;
  scopes.base = proc.inst_prefix;
  scopes.base += SimContext::GenBlockPrefixOf(proc);
  scopes.labels = proc.spawned_in_named_scopes;
  const std::vector<std::string_view>& own = &proc == ctx.CurrentProcess()
                                                 ? ctx.ActiveNamedScopes()
                                                 : proc.saved_named_scopes;
  scopes.labels.insert(scopes.labels.end(), own.begin(), own.end());
  std::string path;
  for (std::string_view label : scopes.labels) {
    if (ctx.FindFunction(label) != nullptr) path.clear();
    if (!path.empty()) path += '.';
    path += label;
    scopes.keys.push_back(scopes.base + path);
  }
  return scopes;
}

bool StandsIn(const StandingScopes& scopes, std::string_view key) {
  if (std::ranges::find(scopes.keys, key) != scopes.keys.end()) return true;
  const std::size_t kDot = key.rfind('.');
  const std::string_view kLeaf = key.substr(kDot + 1);
  if (std::ranges::find(scopes.labels, kLeaf) != scopes.labels.end()) {
    return false;
  }
  std::string_view inner = scopes.base;
  if (!scopes.keys.empty()) {
    inner = scopes.keys.back();
  } else if (inner.ends_with('.')) {
    inner.remove_suffix(1);
  }
  return key.substr(0, kDot == std::string_view::npos ? 0 : kDot) == inner;
}

std::vector<std::string> CandidateKeys(const std::string& path,
                                       const Process& self, SimContext& ctx) {
  std::vector<std::string> keys;
  const StandingScopes kMine = ScopesOf(self, ctx);
  for (std::size_t i = kMine.labels.size(); i-- > 0;) {
    keys.push_back(kMine.keys[i] + "." + path);
    if (ctx.FindFunction(kMine.labels[i]) != nullptr) break;
  }
  for (std::size_t i = self.gen_prefixes.size(); i-- > 0;) {
    keys.push_back(self.inst_prefix + self.gen_prefixes[i] + path);
  }
  std::string_view prefix = self.inst_prefix;
  for (;;) {
    keys.push_back(std::string(prefix) + path);
    if (prefix.empty()) break;
    const std::size_t kUp = prefix.find_last_of('.', prefix.size() - 2);
    prefix = kUp == std::string_view::npos ? std::string_view{}
                                           : prefix.substr(0, kUp + 1);
  }
  const std::size_t kDot = path.find('.');
  if (kDot != std::string::npos &&
      ctx.IsTopModule(std::string_view(path).substr(0, kDot))) {
    keys.push_back(path.substr(kDot + 1));
  }
  return keys;
}

void DeclareLabelledStmts(const Stmt* s, const std::string& scope,
                          SimContext& ctx) {
  if (s == nullptr) return;
  std::string inner = scope;
  if (!s->label.empty()) {
    inner += s->label;
    ctx.DeclareNamedScope(inner);
    inner += '.';
  }
  ForEachChildStmt(s, [&inner, &ctx](const Stmt* sub) {
    DeclareLabelledStmts(sub, inner, ctx);
  });
}

void DeclareSubroutine(const ModuleItem* func, std::string base,
                       SimContext& ctx) {
  base += func->name;
  ctx.DeclareNamedScope(base);
  base += '.';
  for (const Stmt* s : func->func_body_stmts) {
    DeclareLabelledStmts(s, base, ctx);
  }
}

std::string InnermostGenBlock(const GenBlockPrefixes& prefixes) {
  return prefixes.empty() ? std::string() : std::string(prefixes.back());
}

}  // namespace

std::vector<Process*> ProcessesInDisabledScope(
    const Expr* name, const std::vector<Process*>& procs, SimContext& ctx) {
  const Process* self = ctx.CurrentProcess();
  if (self == nullptr) return procs;
  std::vector<StandingScopes> standing;
  standing.reserve(procs.size());
  for (const Process* proc : procs) standing.push_back(ScopesOf(*proc, ctx));
  const std::string kPath =
      EvaluatedHierarchicalPath(name, ctx, ctx.GetArena());
  for (const std::string& key : CandidateKeys(kPath, *self, ctx)) {
    std::vector<Process*> in;
    for (std::size_t i = 0; i < procs.size(); ++i) {
      if (StandsIn(standing[i], key)) in.push_back(procs[i]);
    }
    if (!in.empty() || ctx.DeclaresNamedScope(key)) return in;
  }
  return {};
}

void DeclareModuleNamedScopes(const RtlirModule& mod,
                              std::string_view inst_prefix, SimContext& ctx) {
  const std::string kInstance(inst_prefix);
  for (const RtlirProcess& proc : mod.processes) {
    DeclareLabelledStmts(
        proc.body, kInstance + InnermostGenBlock(proc.gen_block_prefixes), ctx);
  }
  for (const RtlirGenBlockSubroutine& sub : mod.gen_block_subroutines) {
    DeclareSubroutine(
        sub.decl, kInstance + InnermostGenBlock(sub.gen_block_prefixes), ctx);
  }
  for (const ModuleItem* func : mod.function_decls) {
    if (func->method_class.empty() && DeclaringGenBlock(func, &mod) == nullptr)
      DeclareSubroutine(func, kInstance, ctx);
  }
}

}  // namespace delta
