#include "elaborator/command_line_bind.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast_design.h"

namespace delta {

namespace {

std::unordered_set<std::string_view> DelegatedConfigNames(
    const CompilationUnit& unit) {
  std::unordered_set<std::string_view> names;
  for (const auto* cfg : unit.configs) {
    for (const auto* rule : cfg->rules) {
      if (rule->kind != ConfigRuleKind::kInstance &&
          rule->kind != ConfigRuleKind::kCell) {
        continue;
      }
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

  if (!config.empty()) {
    for (const auto* cfg : in_force) {
      if (cfg->name == config) return elab.Elaborate(cfg);
    }
    diag.Error(SourceLoc::None(),
               std::format("no configuration named '{}' is in force; the "
                           "command line put {} in force",
                           config, in_force.size()),
               Subclause("33.5.4"));
    return nullptr;
  }

  if (in_force.size() > 1) {
    diag.Error(
        SourceLoc::None(),
        std::format("command line puts {} configurations in force; "
                    "'{}' and '{}' each name a design of their own; name one "
                    "with --config",
                    in_force.size(), in_force[0]->name, in_force[1]->name),
        Subclause("33.5.4"));
    return nullptr;
  }

  if (in_force.size() == 1) return elab.Elaborate(in_force.front());

  return elab.Elaborate(top);
}

}  // namespace delta
