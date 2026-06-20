#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

struct BindDirective {
  std::string_view target;
  Expr* target_bit_select = nullptr;
  std::vector<std::string_view> target_instances;
  std::vector<Expr*> target_instance_bit_selects;
  ModuleItem* instantiation = nullptr;
  SourceLoc loc;
};

enum class ConfigRuleKind : uint8_t {
  kDefault,
  kInstance,
  kCell,
};

struct ConfigRule {
  ConfigRuleKind kind = ConfigRuleKind::kDefault;
  std::string_view inst_path;
  std::string_view cell_lib;
  std::string_view cell_name;
  std::vector<std::string_view> liblist;
  std::string_view use_lib;
  std::string_view use_cell;
  bool use_config = false;
  std::vector<std::pair<std::string_view, Expr*>> use_params;
  // Set when the use clause carries an empty override list "#()", which resets
  // every parameter of the bound cell to its module default (§33.4.3). This is
  // distinct from a use clause with no override list at all, where use_params
  // is likewise empty but no reset is intended.
  bool use_param_reset_all = false;
};

struct ConfigDecl {
  std::string_view name;
  SourceRange range;
  std::vector<std::pair<std::string_view, std::string_view>> design_cells;
  std::vector<ConfigRule*> rules;
  std::vector<std::pair<std::string_view, Expr*>> local_params;
  std::string_view library;
};

// 18.5.1: an external constraint block completes a constraint prototype using
// the class scope resolution operator (constraint ClassName::name { ... }). The
// block is declared outside the class, so its placement and pairing with a
// prototype are validated during elaboration.
struct ExternalConstraintBlock {
  std::string_view class_name;
  std::string_view constraint_name;
  SourceLoc loc;
  // 18.5.2: dynamic override specifiers carried on the external constraint
  // block; they must match those on the completing prototype.
  bool is_initial = false;
  bool is_extends = false;
  bool is_final = false;
  // 18.5.10: whether the external constraint block was qualified 'static'. The
  // 'static' qualification must match the completing prototype's, or be absent
  // on both.
  bool is_static = false;
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
  std::vector<ExternalConstraintBlock> external_constraints;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  DelayModeDirective delay_mode_directive = DelayModeDirective::kNone;

  TimeUnit cu_time_unit = TimeUnit::kNs;
  TimeUnit cu_time_prec = TimeUnit::kNs;
  int cu_time_unit_magnitude = 1;
  int cu_time_prec_magnitude = 1;
  bool has_cu_timeunit = false;
  bool has_cu_timeprecision = false;

  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
};

struct ResolvedTimescale {
  TimeUnit unit = TimeUnit::kNs;
  TimeUnit precision = TimeUnit::kNs;
  bool has_unit = false;
  bool has_precision = false;
};

}  // namespace delta
