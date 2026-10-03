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
// An instance inside a generate block is named through the block instance,
// `g[0].pi` (§27.4), where its prefix holds the key its storage is filed
// under.
void AppendProcessLevels(std::string& name, const Process& proc,
                         const SimContext& ctx) {
  std::string prefix(ctx.FindInstancePath(proc.inst_prefix));
  if (prefix.empty()) {
    prefix = proc.inst_prefix;  // "u1.u2." form, empty at top
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  }
  AppendLevel(name, prefix);
  AppendLevel(name, proc.gen_block_name);
}

}  // namespace

// The empty instance prefix is the top level; its registered type name is
// the first top module's name, which doubles as the top instance name. A
// later top's processes carry its name at the head of their prefix
// (Lowerer::LowerParallelTop), which is the whole path then.
static std::string TopLevelName(std::string_view prefix,
                                const SimContext& ctx) {
  bool parallel = ctx.IsParallelTop(prefix.substr(0, prefix.find('.')));
  return std::string(parallel ? "" : ctx.FindInstanceType(""));
}

std::string ProcessHierName(const Process& proc, const SimContext& ctx) {
  std::string name = TopLevelName(proc.inst_prefix, ctx);
  AppendProcessLevels(name, proc, ctx);
  return name;
}

std::string ScopeHierName(const SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  std::string name =
      proc != nullptr ? ProcessHierName(*proc, ctx) : TopLevelName("", ctx);
  for (std::string_view scope : ctx.ActiveNamedScopes()) {
    AppendLevel(name, scope);
  }
  return name;
}

}  // namespace delta
