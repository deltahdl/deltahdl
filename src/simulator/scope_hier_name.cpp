#include "simulator/scope_hier_name.h"

#include <string>
#include <string_view>

#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// `part` joined to `name` as its next level, where it is not empty.
void AppendLevel(std::string& name, std::string_view part) {
  if (part.empty()) return;
  if (!name.empty()) name += '.';
  name += std::string(part);
}

// The instance the process runs in, its `u1.u2.` prefix without the dot it
// ends in, and §27.3's generate block instances it stands in.
void AppendProcessLevels(std::string& name, const Process& proc) {
  std::string prefix = proc.inst_prefix;  // "u1.u2." form, empty at top
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  AppendLevel(name, prefix);
  AppendLevel(name, proc.gen_block_name);
}

}  // namespace

std::string ScopeHierName(const SimContext& ctx) {
  // The empty instance prefix is the top level; its registered type name is
  // the top module's name, which doubles as the top instance name.
  std::string name(ctx.FindInstanceType(""));
  if (Process* proc = ctx.CurrentProcess()) AppendProcessLevels(name, *proc);
  for (std::string_view scope : ctx.ActiveNamedScopes()) {
    AppendLevel(name, scope);
  }
  return name;
}

}  // namespace delta
