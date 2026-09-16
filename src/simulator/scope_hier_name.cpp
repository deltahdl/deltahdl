#include "simulator/scope_hier_name.h"

#include <string>
#include <string_view>

#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

std::string ScopeHierName(const SimContext& ctx) {
  // The empty instance prefix is the top level; its registered type name is
  // the top module's name, which doubles as the top instance name.
  std::string name(ctx.FindInstanceType(""));
  if (Process* proc = ctx.CurrentProcess()) {
    std::string prefix = proc->inst_prefix;  // "u1.u2." form, empty at top
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
    if (!prefix.empty()) {
      if (!name.empty()) name += '.';
      name += prefix;
    }
    // §27.3: a generate block is a level of hierarchy of its own; the
    // innermost prefix the process stands in spells the whole nesting.
    if (!proc->gen_prefixes.empty()) {
      std::string blocks = proc->gen_prefixes.back();
      if (!blocks.empty() && blocks.back() == '.') blocks.pop_back();
      if (!blocks.empty()) {
        if (!name.empty()) name += '.';
        name += blocks;
      }
    }
  }
  for (std::string_view scope : ctx.ActiveNamedScopes()) {
    if (!name.empty()) name += '.';
    name += std::string(scope);
  }
  return name;
}

}  // namespace delta
