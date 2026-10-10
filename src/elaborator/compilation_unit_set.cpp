#include "elaborator/compilation_unit_set.h"

#include <cstddef>
#include <initializer_list>
#include <vector>

#include "common/arena.h"
#include "parser/ast_design.h"

namespace delta {

namespace {

template <typename T>
void Append(std::vector<T>& to, const std::vector<T>& from) {
  to.insert(to.end(), from.begin(), from.end());
}

// The lists of `from` that §3.12.1 makes visible in every unit, and the
// configurations and library declarations that bind them (§33), appended to
// `to`'s.
void AppendDesignElements(const CompilationUnit& from, CompilationUnit& to) {
  Append(to.modules, from.modules);
  Append(to.packages, from.packages);
  Append(to.interfaces, from.interfaces);
  Append(to.programs, from.programs);
  Append(to.udps, from.udps);
  Append(to.configs, from.configs);
  Append(to.libraries, from.libraries);
  Append(to.lib_includes, from.lib_includes);
}

// The lists of `from` that belong to its own compilation-unit scope, appended
// to `to`'s.
void AppendUnitScope(const CompilationUnit& from, CompilationUnit& to) {
  Append(to.cu_items, from.cu_items);
  Append(to.classes, from.classes);
  Append(to.checkers, from.checkers);
  Append(to.bind_directives, from.bind_directives);
  Append(to.external_constraints, from.external_constraints);
  to.triggered_names.insert(from.triggered_names.begin(),
                            from.triggered_names.end());
  to.dotted_escaped_names.insert(from.dotted_escaped_names.begin(),
                                 from.dotted_escaped_names.end());
}

// `unit` with its design elements replaced by `pooled`'s.
CompilationUnit* ViewOver(const CompilationUnit& unit,
                          const CompilationUnit& pooled, Arena& arena) {
  auto* view = arena.Create<CompilationUnit>(unit);
  view->modules = pooled.modules;
  view->packages = pooled.packages;
  view->interfaces = pooled.interfaces;
  view->programs = pooled.programs;
  view->udps = pooled.udps;
  view->configs = pooled.configs;
  view->libraries = pooled.libraries;
  view->lib_includes = pooled.lib_includes;
  return view;
}

}  // namespace

CompilationUnitSet PoolCompilationUnits(
    const std::vector<CompilationUnit*>& units, Arena& arena) {
  CompilationUnit pooled;
  for (const auto* unit : units) AppendDesignElements(*unit, pooled);

  CompilationUnitSet set;
  set.units = units;
  for (size_t k = 0; k < units.size(); ++k) {
    set.views.push_back(ViewOver(*units[k], pooled, arena));
    for (const auto* decls : {&units[k]->modules, &units[k]->interfaces,
                              &units[k]->programs, &units[k]->checkers}) {
      for (const auto* decl : *decls) set.owner[decl] = k;
    }
  }
  // The first unit's directives and time scale stand for the merged view,
  // which no design element is elaborated under.
  set.merged = ViewOver(*units.front(), pooled, arena);
  for (size_t k = 1; k < units.size(); ++k) {
    AppendUnitScope(*units[k], *set.merged);
  }
  set.tables.resize(units.size());
  set.current = units.size();
  return set;
}

}  // namespace delta
