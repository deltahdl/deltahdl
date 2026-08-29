#include "elaborator/command_line_bind.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast.h"

namespace delta {

namespace {

// The names of the configurations that some configuration's instance clause
// delegates to. Whether a use clause names a configuration at all rather than
// an ordinary cell is §33.2.1's question, so it is asked there instead of
// being answered here by looking for the ':config' extension alone -- a name
// that reaches no other design element names the configuration of that name
// without carrying the extension.
std::unordered_set<std::string_view> DelegatedConfigNames(
    const CompilationUnit& unit) {
  std::unordered_set<std::string_view> names;
  for (const auto* cfg : unit.configs) {
    for (const auto* rule : cfg->rules) {
      if (rule->kind != ConfigRuleKind::kInstance) continue;
      if (!UseClauseNamesConfig(rule, cfg, &unit)) continue;
      names.insert(rule->use_cell);
    }
  }
  return names;
}

}  // namespace

std::vector<const ConfigDecl*> ConfigsInForce(const CompilationUnit& unit) {
  auto delegated = DelegatedConfigNames(unit);
  std::vector<const ConfigDecl*> in_force;
  for (const auto* cfg : unit.configs) {
    if (cfg->design_cells.empty()) continue;
    if (delegated.contains(cfg->name)) continue;
    in_force.push_back(cfg);
  }
  return in_force;
}

RtlirDesign* ElaborateCommandLine(Elaborator& elab, const CompilationUnit& unit,
                                  std::string_view top, std::string_view config,
                                  DiagEngine& diag) {
  auto in_force = ConfigsInForce(unit);

  // §33.5.4: the config to be used is one of the two things the command line
  // gives a binding tool, so a named one settles the design outright and the
  // count of configurations in force decides nothing.
  if (!config.empty()) {
    for (const auto* cfg : in_force) {
      if (cfg->name == config) return elab.Elaborate(cfg);
    }
    // The name came from the command line rather than from a source
    // description, so there is nothing written anywhere for the report to
    // stand at. A configuration the unit holds but that no design statement
    // gives a design, or that another configuration delegates an instance to,
    // is not in force and is not selectable: ConfigsInForce is what says which
    // names this option takes.
    diag.Error(SourceLoc::None(),
               std::format("no configuration named '{}' is in force; the "
                           "command line put {} in force",
                           config, in_force.size()),
               Subclause("33.5.4"));
    return nullptr;
  }

  if (in_force.size() > 1) {
    // Each of them names a whole design, and a run builds one. Which was meant
    // is not something the source descriptions record, so the command line is
    // reported rather than one of them being picked for the user.
    diag.Error(
        SourceLoc::None(),
        std::format("command line puts {} configurations in force; "
                    "'{}' and '{}' each name a design of their own; name one "
                    "with --config",
                    in_force.size(), in_force[0]->name, in_force[1]->name),
        Subclause("33.5.4"));
    return nullptr;
  }

  // The design statement names the top-level cell, whatever cells the rest of
  // the source descriptions on the command line leave uninstantiated.
  if (in_force.size() == 1) return elab.Elaborate(in_force.front());

  return elab.Elaborate(top);
}

}  // namespace delta
