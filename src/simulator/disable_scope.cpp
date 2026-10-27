#include "simulator/disable_scope.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/eval_function_hier.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// The named scopes a process stands in, outermost first: their labels, and the
// key each stands under, `base` -- its instance's prefix and its generate
// block's -- then the labels from the procedure or the subroutine it runs in
// to the scope, a subroutine's own name starting the path afresh as
// ActiveNamedScopePath's does.
struct StandingScopes {
  std::string base;
  std::vector<std::string_view> labels;
  std::vector<std::string> keys;
};

StandingScopes ScopesOf(const Process& proc, SimContext& ctx) {
  StandingScopes scopes;
  scopes.base = proc.inst_prefix;
  scopes.base += SimContext::GenBlockPrefixOf(proc);
  scopes.labels = &proc == ctx.CurrentProcess() ? ctx.ActiveNamedScopes()
                                                : proc.saved_named_scopes;
  std::string path;
  for (std::string_view label : scopes.labels) {
    if (ctx.FindFunction(label) != nullptr) path.clear();
    if (!path.empty()) path += '.';
    path += label;
    scopes.keys.push_back(scopes.base + path);
  }
  return scopes;
}

// Whether `scopes` stands in the scope keyed `key`: one it is in, or one it
// was registered in before entering it -- a labelled loop's block, or the
// block or task a fork branch begins with -- whose label is none of those it
// is in and which stands directly in the innermost scope it is in.
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

// The keys the name written as `path` may stand for, nearest first, as §23.8
// searches for it from where the running process `self` stands.
std::vector<std::string> CandidateKeys(const std::string& path,
                                       const Process& self, SimContext& ctx) {
  std::vector<std::string> keys;
  const StandingScopes kMine = ScopesOf(self, ctx);
  // The scopes the disable stands in, innermost first, back to the procedure
  // or the subroutine it is written in.
  for (std::size_t i = kMine.labels.size(); i-- > 0;) {
    keys.push_back(kMine.keys[i] + "." + path);
    if (ctx.FindFunction(kMine.labels[i]) != nullptr) break;
  }
  // §27.4 with §23.9: the generate blocks it stands in, innermost first.
  for (std::size_t i = self.gen_prefixes.size(); i-- > 0;) {
    keys.push_back(self.inst_prefix + self.gen_prefixes[i] + path);
  }
  // Its instance, then each instance holding that one.
  std::string_view prefix = self.inst_prefix;
  for (;;) {
    keys.push_back(std::string(prefix) + path);
    if (prefix.empty()) break;
    const std::size_t kUp = prefix.find_last_of('.', prefix.size() - 2);
    prefix = kUp == std::string_view::npos ? std::string_view{}
                                           : prefix.substr(0, kUp + 1);
  }
  // §23.6: a path headed by a top-level module's name is read from that top,
  // whose own scopes are keyed under no prefix.
  const std::size_t kDot = path.find('.');
  if (kDot != std::string::npos &&
      ctx.IsTopModule(std::string_view(path).substr(0, kDot))) {
    keys.push_back(path.substr(kDot + 1));
  }
  return keys;
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
    if (!in.empty()) return in;
  }
  return {};
}

}  // namespace delta
