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

// The instance whose `u1.u2.` prefix is `inst_prefix`, without the dot it
// ends in. An instance inside a generate block is named through the block
// instance, `g[0].pi` (§27.4), where its prefix holds the key its storage is
// filed under.
void AppendInstanceLevels(std::string& name, std::string_view inst_prefix,
                          const SimContext& ctx) {
  std::string prefix(ctx.FindInstancePath(inst_prefix));
  if (prefix.empty()) {
    prefix = inst_prefix;  // "u1.u2." form, empty at top
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  }
  AppendLevel(name, prefix);
}

// The instance the process runs in and §27.3's generate block instances it
// stands in.
void AppendProcessLevels(std::string& name, const Process& proc,
                         const SimContext& ctx) {
  AppendInstanceLevels(name, proc.inst_prefix, ctx);
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

// §21.2.1.5: with no process running, as a static variable's initializer is
// evaluated while its instance is lowered, the name is that instance's
// (SimContext::ActiveInstancePrefix), as %l's binding is (eval_format.cpp).
static std::string LoweringHierName(const SimContext& ctx) {
  std::string prefix = ctx.ActiveInstancePrefix();
  std::string name = TopLevelName(prefix, ctx);
  AppendInstanceLevels(name, prefix, ctx);
  return name;
}

std::string ScopeHierName(const SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  std::string name =
      proc != nullptr ? ProcessHierName(*proc, ctx) : LoweringHierName(ctx);
  for (std::string_view scope : ctx.ActiveNamedScopes()) {
    AppendLevel(name, scope);
  }
  return name;
}

}  // namespace delta
