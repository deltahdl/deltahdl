#include "simulator/scope_hier_name.h"

#include <string>
#include <string_view>

#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

void AppendLevel(std::string& name, std::string_view part) {
  if (part.empty()) return;
  if (!name.empty()) name += '.';
  name += std::string(part);
}

void AppendInstanceLevels(std::string& name, std::string_view inst_prefix,
                          const SimContext& ctx) {
  std::string prefix(ctx.FindInstancePath(inst_prefix));
  if (prefix.empty()) {
    prefix = inst_prefix;
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  }
  AppendLevel(name, prefix);
}

void AppendProcessLevels(std::string& name, const Process& proc,
                         const SimContext& ctx) {
  AppendInstanceLevels(name, proc.inst_prefix, ctx);
  AppendLevel(name, proc.gen_block_name);
}

}  // namespace

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
