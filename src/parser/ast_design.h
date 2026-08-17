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

// One config_rule_statement (§33.4.1): the clause kind, what it selects, and
// where the clause begins. A report about the clause carries that position, so
// a configuration holding several default, instance or cell clauses says which
// of them the report is about.
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
  // Set when the use clause carries an empty override list "#()", which resets
  // every parameter of the bound cell to its module default (§33.4.3). This is
  // distinct from a use clause with no override list at all, where use_params
  // is likewise empty but no reset is intended.
  bool use_param_reset_all = false;
};

// One cell a design statement names (§33.4.1.1): a cell_identifier, the
// library_identifier qualifying it where the statement wrote one, and where
// the cell_identifier stands. A report about the cell carries that position,
// so a configuration whose design statement names several cells says which of
// them the report is about.
struct ConfigDesignCell {
  std::string_view library;
  std::string_view cell;
  SourceLoc loc;
};

struct ConfigDecl {
  std::string_view name;
  SourceRange range;
  std::vector<ConfigDesignCell> design_cells;
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
  // 18.5.1: the top-level relation expressions of the external block's body,
  // captured so elaboration can complete the matching prototype with them. A
  // prototype so completed then constrains randomization like an in-class
  // constraint block; a prototype left without a block keeps an empty set and
  // behaves as an empty constraint (equivalent to the constant expression 1).
  std::vector<Expr*> constraint_exprs;
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

// §22.10: applies the cell-module tag. The preprocessor decides which modules
// the `celldefine/`endcelldefine regions covered and hands the names over; this
// is the step that puts the tag on the declarations the parser built. It lives
// here rather than in the driver so that every path which preprocesses and then
// parses -- the compiler, and anything else assembling a compilation unit --
// tags cells the same way instead of repeating the match.
inline void MarkCellModules(CompilationUnit* cu,
                            const std::vector<std::string>& cell_module_names) {
  if (cu == nullptr) return;
  for (auto* mod : cu->modules) {
    for (const auto& cell_name : cell_module_names) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
}

// Every design element §3.2 defines, which is what §33.2.1 makes a cell.
// Moving them from one compilation unit onto another is what makes a separately
// parsed source description part of the unit a design is bound against, so
// every path that assembles a unit out of more than one parse shares this step
// rather than restating which element kinds a library holds. Nothing is copied:
// the declarations stay in the arena that parsed them and the target gains
// pointers to them.
//
// §33.2.1 rules that "a library is a named collection of cells" and that "a
// cell is a design element (see 3.2), such as a module, primitive, interface,
// program, package, or configuration". Its six are introduced by "such as", and
// the definition it defers to is §3.2's, which names seven: "a SystemVerilog
// module (see Clause 23), program (see Clause 24), interface (see Clause 25),
// checker (see Clause 17), package (see Clause 26), primitive (see Clause 28)
// or configuration (see Clause 33)". Reading §33.2.1's examples as the whole
// set is what left the checker out of this function.
//
// The lists CompilationUnit holds that are not moved are left behind on
// purpose, for two different reasons. `classes`, `cu_items`, `bind_directives`
// and `external_constraints` hold what a source declared outside every design
// element, and §3.12.1 rules that "items defined in the compilation-unit scope
// cannot be accessed by name from outside the compilation unit", so they stay
// with the unit that parsed them. `libraries` and `lib_includes` stay because
// they are not a source description's to contribute: §33.3.1 has the library
// map file "automatically read by the parser prior to parsing any source files
// specified on the command line", and Syntax 33-2 gives library_declaration and
// include_statement only in library_text.
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
}

}  // namespace delta
