#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

struct ClassMember;

struct BindTargetSegment {
  std::string_view name;
  std::vector<Expr*> selects;
};

struct BindTargetInstance {
  std::string_view path;
  bool from_root = false;
  std::vector<BindTargetSegment> segments;
};

struct BindDirective {
  BindTargetInstance target;
  std::vector<BindTargetInstance> target_instances;
  ModuleItem* instantiation = nullptr;
  SourceLoc loc;
  bool in_generate_block = false;
};

enum class ConfigRuleKind : uint8_t {
  kDefault,
  kInstance,
  kCell,
};

struct ConfigRule {
  ConfigRuleKind kind = ConfigRuleKind::kDefault;
  SourceLoc loc;
  std::string_view inst_path;
  std::string_view cell_lib;
  std::string_view cell_name;
  std::vector<std::string_view> liblist;
  std::string_view use_lib;
  std::string_view use_cell;
  bool use_config = false;
  std::vector<std::pair<std::string_view, Expr*>> use_params;
  bool use_param_reset_all = false;
};

struct ConfigDesignCell {
  std::string_view library;
  std::string_view cell;
  SourceLoc loc;
};

struct ConfigLocalparam {
  std::string_view name;
  Expr* init_expr = nullptr;
  DataType data_type;
  bool is_type = false;
  SourceLoc loc;
};

struct ConfigDecl {
  std::string_view name;
  SourceRange range;
  std::vector<ConfigDesignCell> design_cells;
  std::vector<ConfigRule*> rules;
  std::vector<ConfigLocalparam> local_params;
  std::string_view library;
};

struct ExternalConstraintBlock {
  std::string_view class_name;
  std::string_view constraint_name;
  SourceLoc loc;
  bool is_initial = false;
  bool is_extends = false;
  bool is_final = false;
  bool is_static = false;
  ClassMember* body = nullptr;
  const std::vector<ModuleItem*>* scope_items = nullptr;
};

struct TimeLiteralSite {
  Expr* literal = nullptr;
  const ModuleDecl* module = nullptr;
  const PackageDecl* package = nullptr;
};

struct ScopePrefix {
  std::string_view name;
  SourceLoc loc;
};

struct CompilationUnit {
  std::vector<ModuleDecl*> modules;
  std::vector<PackageDecl*> packages;
  std::vector<ModuleDecl*> interfaces;
  std::vector<ModuleDecl*> programs;
  std::vector<ClassDecl*> classes;
  std::vector<UdpDecl*> udps;
  std::vector<ModuleDecl*> checkers;
  std::vector<ConfigDecl*> configs;
  std::vector<LibraryDecl*> libraries;
  std::vector<IncludeStmt*> lib_includes;
  std::vector<BindDirective*> bind_directives;
  std::vector<ModuleItem*> cu_items;
  std::unordered_set<std::string_view> triggered_names;
  std::unordered_set<std::string_view> dotted_escaped_names;
  std::vector<ExternalConstraintBlock> external_constraints;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;
  bool default_decay_time_is_real = false;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  DelayModeDirective delay_mode_directive = DelayModeDirective::kNone;

  TimeUnit cu_time_unit = TimeUnit::kNs;
  TimeUnit cu_time_prec = TimeUnit::kNs;
  int cu_time_unit_magnitude = 1;
  int cu_time_prec_magnitude = 1;
  bool has_cu_timeunit = false;
  SourceLoc cu_timeunit_loc;
  bool has_cu_timeprecision = false;
  SourceLoc cu_timeprecision_loc;
  bool has_read_cu_item = false;

  std::vector<TimeLiteralSite> time_literals;

  bool has_preproc_global_precision = false;
  TimeUnit preproc_global_precision = TimeUnit::kNs;
  int preproc_global_precision_magnitude = 1;

  bool DeclaresNothing() const {
    return modules.empty() && programs.empty() && packages.empty() &&
           cu_items.empty() && classes.empty();
  }

  std::vector<ScopePrefix> scope_prefixes;
};

inline void MarkCellModules(CompilationUnit* cu,
                            const std::vector<std::string>& cell_module_names) {
  for (auto* mod : cu->modules) {
    for (const auto& cell_name : cell_module_names) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
}

inline const ModuleDirectives* DirectivesAtHeader(
    std::string_view name, const std::vector<ModuleDirectives>& directives,
    bool is_package = false) {
  for (const auto& d : directives) {
    if (name == d.module && d.is_package == is_package) return &d;
  }
  return nullptr;
}

inline void ApplyModuleDirectives(
    CompilationUnit* cu, const std::vector<ModuleDirectives>& directives) {
  for (auto* mod : cu->modules) {
    const ModuleDirectives* d = DirectivesAtHeader(mod->name, directives);
    if (d == nullptr) continue;
    mod->has_module_directives = true;
    mod->default_decay_time = d->decay_ticks;
    mod->default_decay_time_infinite = d->decay_infinite;
    mod->default_decay_time_is_real = d->decay_is_real;
    mod->default_decay_time_real = d->decay_real;
    mod->default_trireg_strength = d->strength;
    mod->has_default_trireg_strength = d->has_strength;
    mod->delay_mode = d->delay_mode;
  }
  for (const auto* list : {&cu->modules, &cu->interfaces, &cu->programs}) {
    for (auto* mod : *list) {
      const ModuleDirectives* d = DirectivesAtHeader(mod->name, directives);
      if (d == nullptr) continue;
      mod->has_directive_timescale = d->has_timescale;
      mod->directive_timescale = d->timescale;
      mod->has_net_directives = true;
      mod->default_nettype = d->default_nettype;
      mod->unconnected_drive = d->unconnected_drive;
    }
  }
  for (auto* pkg : cu->packages) {
    const ModuleDirectives* d = DirectivesAtHeader(pkg->name, directives, true);
    if (d == nullptr) continue;
    pkg->has_directive_timescale = d->has_timescale;
    pkg->directive_timescale = d->timescale;
  }
}

inline void AppendCellDeclarations(CompilationUnit& target,
                                   const CompilationUnit& src) {
  target.modules.insert(target.modules.end(), src.modules.begin(),
                        src.modules.end());
  target.interfaces.insert(target.interfaces.end(), src.interfaces.begin(),
                           src.interfaces.end());
  target.programs.insert(target.programs.end(), src.programs.begin(),
                         src.programs.end());
  target.checkers.insert(target.checkers.end(), src.checkers.begin(),
                         src.checkers.end());
  target.udps.insert(target.udps.end(), src.udps.begin(), src.udps.end());
  target.packages.insert(target.packages.end(), src.packages.begin(),
                         src.packages.end());
  target.configs.insert(target.configs.end(), src.configs.begin(),
                        src.configs.end());
  target.dotted_escaped_names.insert(src.dotted_escaped_names.begin(),
                                     src.dotted_escaped_names.end());
  for (const TimeLiteralSite& site : src.time_literals) {
    if (site.module != nullptr || site.package != nullptr) {
      target.time_literals.push_back(site);
    }
  }
}

inline void AppendCompilationUnitDeclarations(CompilationUnit& target,
                                              const CompilationUnit& src) {
  target.cu_items.insert(target.cu_items.end(), src.cu_items.begin(),
                         src.cu_items.end());
  target.classes.insert(target.classes.end(), src.classes.begin(),
                        src.classes.end());
  target.bind_directives.insert(target.bind_directives.end(),
                                src.bind_directives.begin(),
                                src.bind_directives.end());
  target.external_constraints.insert(target.external_constraints.end(),
                                     src.external_constraints.begin(),
                                     src.external_constraints.end());
  target.scope_prefixes.insert(target.scope_prefixes.end(),
                               src.scope_prefixes.begin(),
                               src.scope_prefixes.end());
  for (const TimeLiteralSite& site : src.time_literals) {
    if (site.module == nullptr && site.package == nullptr) {
      target.time_literals.push_back(site);
    }
  }
  if (src.has_cu_timeunit && !target.has_cu_timeunit) {
    target.cu_time_unit = src.cu_time_unit;
    target.cu_time_unit_magnitude = src.cu_time_unit_magnitude;
    target.has_cu_timeunit = true;
    target.cu_timeunit_loc = src.cu_timeunit_loc;
  }
  if (src.has_cu_timeprecision && !target.has_cu_timeprecision) {
    target.cu_time_prec = src.cu_time_prec;
    target.cu_time_prec_magnitude = src.cu_time_prec_magnitude;
    target.has_cu_timeprecision = true;
    target.cu_timeprecision_loc = src.cu_timeprecision_loc;
  }
}

}  // namespace delta
