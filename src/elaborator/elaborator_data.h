#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/compilation_unit_set.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/interconnect_merges.h"
#include "elaborator/module_scope_names.h"
#include "elaborator/pending_generate.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"

namespace delta {

class UnitHierHeadNames;

class Arena;
class DiagEngine;
struct ClassDecl;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
struct RtlirModuleInst;
struct RtlirParamDecl;

inline constexpr int64_t kDefaultMaxGenerateIterations = 262144;

struct DefparamWriterBlock {
  RtlirModule* holder;
  HierPath steps;
  const RtlirModule* element = nullptr;
  bool arrayed_interface = false;
};
using DefparamWriterBlocks =
    std::unordered_map<const RtlirModule*, DefparamWriterBlock>;

class ElaboratorData {
 public:
  struct DeclaredDim {
    int64_t left = 0;
    int64_t right = 0;

    [[nodiscard]] bool IsDescending() const { return left >= right; }
  };

  struct VarArrayInfo {
    DataTypeKind elem_type = DataTypeKind::kImplicit;
    uint32_t unpacked_size = 0;
    uint32_t num_unpacked_dims = 0;
    uint32_t elem_width = 0;
    bool elem_is_signed = false;
    bool elem_is_4state = true;
    bool is_dynamic = false;
    bool is_assoc = false;
    std::string_view assoc_index_type;
    std::vector<uint32_t> dim_sizes;
    std::vector<DeclaredDim> declared_dims;
    bool is_queue = false;
    bool elements_are_queues = false;
    std::vector<std::optional<uint32_t>> unpacked_shape = {};
    std::string_view elem_type_name = {};
    bool elem_is_unpacked_aggregate = false;
    const DataType* elem_data_type = nullptr;
  };

  struct GenerateScopeSaver {
    explicit GenerateScopeSaver(ElaboratorData& e)
        : e_(e),
          prefix_(std::move(e.gen_prefix_)),
          scopes_(std::move(e.gen_prefix_scopes_)),
          path_(std::move(e.gen_block_path_)),
          consts_(std::move(e.gen_loop_consts_)),
          const_scope_(std::move(e.gen_const_scope_)) {
      e.gen_prefix_.clear();
      e.gen_prefix_scopes_.clear();
      e.gen_block_path_.clear();
      e.gen_loop_consts_.clear();
      e.gen_const_scope_.clear();
    }
    ~GenerateScopeSaver() {
      e_.gen_prefix_ = std::move(prefix_);
      e_.gen_prefix_scopes_ = std::move(scopes_);
      e_.gen_block_path_ = std::move(path_);
      e_.gen_loop_consts_ = std::move(consts_);
      e_.gen_const_scope_ = std::move(const_scope_);
    }
    GenerateScopeSaver(const GenerateScopeSaver&) = delete;
    GenerateScopeSaver& operator=(const GenerateScopeSaver&) = delete;

   private:
    ElaboratorData& e_;
    std::string prefix_;
    GenBlockPrefixes scopes_;
    HierPath path_;
    GenBlockConsts consts_;
    ScopeMap const_scope_;
  };

 protected:
  friend struct ItemElaborationStateSaver;
  friend struct UnitScopeTables;

  CompilationUnitSet units_;

  std::vector<std::unordered_set<std::string_view>> enclosing_scope_names_;
  std::unordered_set<std::string_view> pending_enclosing_scope_;
  bool has_pending_enclosing_scope_ = false;
  std::unordered_map<const ModuleDecl*, std::unordered_set<std::string_view>>
      nested_decl_scope_names_;
  std::unordered_map<const ModuleDecl*, std::unordered_set<std::string>>
      nested_decl_names_above_;
  void RecordNestedDeclNamesAbove(const std::vector<ModuleItem*>& items);
  void BeginNestedDeclScope(const ModuleDecl* nested,
                            std::unordered_set<std::string_view> at_instance);
  Expr* nested_default_disable_iff_ = nullptr;
  Expr* inherited_default_disable_iff_ = nullptr;
  std::vector<EventExpr> nested_default_clock_;
  std::vector<EventExpr> inherited_default_clock_;
  BoundCheckerFormals pending_checker_actuals_;
  ActualsByFormal pending_checker_tree_actuals_;
  std::unordered_map<const RtlirModule*, ActualsByFormal> checker_tree_actuals_;
  TypedefMap pending_type_param_types_;

  std::unordered_set<std::string_view> declared_names_;
  std::unordered_set<std::string_view> dpi_import_names_;
  std::unordered_map<const RtlirModule*, ModuleScopeNames> module_scope_names_;
  void SwapModuleScopeNames(ModuleScopeNames& names);
  std::unordered_set<std::string_view> active_loop_genvars_;
  std::unordered_set<std::string_view> net_names_;
  std::unordered_map<std::string_view, SourceLoc> cont_assign_targets_;
  UwireDrivers uwire_drivers_;
  UnitUwireDrivers unit_uwire_drivers_;
  std::unordered_map<std::string_view, SourceLoc> proc_assign_targets_;
  std::unordered_map<std::string_view, DataTypeKind> var_types_;
  std::unordered_map<std::string_view, VarArrayInfo> var_array_info_;
  std::unordered_map<std::string_view, VarArrayInfo> net_array_info_;
  std::unordered_map<std::string_view, const ModuleItem*> dpi_import_decls_;

  std::unordered_set<std::string_view> packed_array_vars_;
  std::unordered_set<std::string_view> specparam_names_;
  std::unordered_set<std::string_view> enum_var_names_;
  std::unordered_set<std::string_view> enum_member_names_;
  std::unordered_set<std::string_view> enum_keyed_arrays_;
  std::string_view inline_enum_list_key_;
  std::unordered_set<std::string_view> const_names_;
  std::unordered_set<std::string_view> const_var_names_;

  std::unordered_map<std::string_view, DataTypeKind> forward_typedef_kinds_;
  std::unordered_set<std::string_view> class_names_;
  std::unordered_map<std::string_view, const ClassDecl*> module_classes_;
  std::unordered_set<std::string_view> parameterized_class_names_;
  std::unordered_set<std::string_view> class_var_names_;
  std::unordered_map<std::string_view, std::string_view> class_var_types_;
  std::unordered_set<std::string_view> var_init_names_;
  std::unordered_map<std::string_view, SourceLoc> output_port_targets_;
  std::unordered_map<std::string_view, SourceLoc> force_release_targets_;
  std::unordered_set<std::string_view> nettype_net_names_;
  std::unordered_set<std::string_view> nettype_names_;
  std::unordered_map<std::string_view, std::string_view> nettype_resolve_funcs_;
  std::unordered_map<std::string_view, std::string_view> nettype_canonical_;
  std::unordered_set<std::string_view> interconnect_names_;
  InterconnectMerges interconnect_merges_;
  std::unordered_set<std::string_view> scalar_var_names_;
  std::unordered_set<std::string_view> real_var_names_;
  std::unordered_set<std::string_view> real_param_names_;
  std::unordered_map<std::string_view, VarSelectShape> var_select_shapes_;
  std::unordered_set<std::string_view> task_names_;
  std::unordered_set<std::string_view> let_names_;
  std::unordered_set<std::string_view> sequence_names_;
  PropertyRegistry property_registry_;

  std::unordered_map<std::string_view, const ModuleItem*> func_decls_;
  InferenceFuncs inference_funcs_;
  std::vector<const ModuleDecl*> module_decl_path_;
  std::unordered_set<std::string_view> chandle_result_funcs_;
  std::unordered_map<std::string_view, std::string_view> var_named_types_;
  using AliasBitRef = std::pair<std::string_view, uint32_t>;
  std::set<std::pair<AliasBitRef, AliasBitRef>> alias_bit_pairs_;

  std::unordered_set<std::string_view> non_ansi_complete_ports_;
  std::unordered_map<std::string_view, uint32_t> non_ansi_partial_ports_;
  std::unordered_set<std::string_view> non_ansi_signed_ports_;

  std::unordered_set<std::string_view> ansi_port_names_;

  std::unordered_map<std::string_view, std::string_view> interface_inst_types_;
  std::unordered_map<std::string_view, std::string_view>
      vi_var_interface_types_;
  std::unordered_map<std::string_view, std::string_view> vi_var_modports_;
  std::unordered_map<std::string_view, DataTypeKind> vi_expr_types_;
  std::unordered_map<std::string_view, std::size_t> vi_array_dims_;

  std::unordered_map<std::string_view, std::vector<int64_t>>
      vi_var_param_values_;
  std::unordered_map<std::string_view, std::vector<int64_t>>
      interface_inst_param_values_;
  std::unordered_set<std::string_view> vi_external_defparam_insts_;

  std::unordered_set<std::string_view> checker_inst_names_;
  std::unordered_set<std::string_view> program_inst_names_;
  std::unordered_set<std::string_view> auto_task_func_names_;
  std::unordered_map<std::string_view, ModuleDecl*> nested_module_decls_;
  std::unordered_map<std::string_view, ModuleDecl*> enclosing_nested_decls_;
  std::unordered_map<std::string_view, ModuleDecl*>
      pending_enclosing_nested_decls_;
  std::unordered_map<std::string_view, ModuleDecl*> NestedDeclsSeenInside()
      const;
  void TakeNestedDeclInheritance();

  ProvidedNameCache pkg_provided_names_;
  std::shared_ptr<const UnitHierHeadNames> unit_hier_head_names_;

  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>
      explicit_imports_;

  std::vector<std::string_view> wildcard_packages_;

  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed_;

  struct ClockingSignalInfo {
    Direction direction;
    std::vector<std::string_view> associated;
  };
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, ClockingSignalInfo>>
      clocking_signals_;

  bool global_clocking_in_scope_ = false;

  struct GlobalClockingScope {
    const std::vector<EventExpr>* events = nullptr;
    std::string inst_path;
  };
  std::vector<GlobalClockingScope> global_clocking_scopes_;

  const std::vector<EventExpr>* module_global_clocking_event_ = nullptr;

  std::vector<PendingGenerate> pending_generates_;

  struct DefparamSite {
    const ModuleItem* item;
    std::string_view prefix;
    GenBlockPrefixes scopes;
    GenBlockConsts consts;
    HierPath path;
  };

  std::unordered_map<RtlirModule*, std::vector<DefparamSite>>
      generate_defparams_;

  std::unordered_set<const BindDirective*> generate_binds_;

  std::set<
      std::tuple<RtlirModule*, const ModuleItem*, size_t, std::string_view>>
      applied_defparams_;

  DefparamWriterBlocks defparam_writer_blocks_;
  void IsolateArrayElement(const RtlirModule& parent, RtlirModuleInst& elem,
                           Arena& arena);
  void IsolateArrayElements(RtlirModule& mod, Arena& arena,
                            const CompilationUnit& unit);
  bool WritesDefparams(const CompilationUnit& unit);
  std::optional<bool> declares_defparams_;
  struct BlockParamDefparam {
    Expr* value;
    const ScopeMap& scope;
    SourceLoc loc;
    DiagEngine& diag;
    Arena& arena;
  };
  bool ApplyBlockParamDefparam(RtlirModule* mod, const HierPath& writer,
                               const HierPath& path,
                               const BlockParamDefparam& d);
  RtlirModule* CopyModuleTree(
      RtlirModule* mod, Arena& arena,
      std::unordered_map<const RtlirModule*, RtlirModule*>& copies);
  std::vector<RtlirModule*> defparam_top_roots_;
  std::vector<const ModuleDecl*> top_decls_;

  std::unordered_map<std::string_view, const ModuleItem*>
      deferred_subroutine_map_;

  std::string gen_prefix_;
  std::vector<std::string_view> gen_prefix_scopes_;
  HierPath gen_block_path_;

  ScopeMap gen_const_scope_;

  std::vector<std::pair<std::string_view, int64_t>> gen_loop_consts_;

  bool elab_simulation_blocked_ = false;

  std::string elab_last_severity_;
  std::string elab_last_severity_msg_;
  std::string elab_last_severity_scope_;
  SourceLoc elab_last_severity_loc_;

  std::vector<std::string> library_order_;

  bool library_order_strict_ = false;

  int64_t max_generate_iterations_ = kDefaultMaxGenerateIterations;

  struct CellUseOverride {
    std::string src_lib;
    std::string use_lib;
    std::string use_cell;
  };
  std::unordered_map<std::string, CellUseOverride> cell_clause_use_overrides_;

  std::vector<std::pair<std::string, const ConfigDecl*>> config_delegations_;
  std::unordered_map<std::string, const ConfigDecl*> cell_config_delegations_;

  std::unordered_map<std::string, std::vector<std::string>>
      cell_clause_liblist_overrides_;

  std::vector<std::pair<std::string, std::vector<std::string>>>
      instance_liblist_overrides_;

  std::vector<std::tuple<std::string, std::string, std::string>>
      instance_use_overrides_;

  std::vector<std::tuple<std::string, std::string, std::string>>
      instance_bind_overrides_;

  bool ReportConfigRuleBindingNothing(CompilationUnit* unit,
                                      const ModuleItem* item,
                                      DiagEngine& diag) const;
  std::optional<std::pair<std::string, std::string>> UseTargetInForce(
      CompilationUnit* unit, const std::string& path,
      std::string_view name) const;

  struct ConfigParamOverride {
    std::string inst_path;
    bool reset_all = false;
    std::vector<std::pair<std::string_view, Expr*>> params;
    SourceLoc loc;
  };
  std::vector<ConfigParamOverride> instance_param_overrides_;
  std::vector<ConfigParamOverride> cell_param_overrides_;

  ScopeMap config_localparam_scope_;

  std::unordered_map<std::string, ScopeMap> config_ancestor_scopes_;

  std::vector<std::pair<std::string, std::vector<std::string>>>
      cell_liblist_bindings_;
  void RecordCellClauseListBinding(std::string_view cell);
  const std::vector<std::string>* SelectedLiblist(std::string_view name) const;

  struct ConfigRuleTables {
    std::vector<std::string> library_order;
    bool library_order_strict = false;
    decltype(cell_clause_use_overrides_) cell_uses;
    decltype(cell_clause_liblist_overrides_) cell_liblists;
    decltype(instance_liblist_overrides_) instance_liblists;
    decltype(instance_use_overrides_) instance_uses;
    decltype(instance_bind_overrides_) instance_binds;
    decltype(instance_param_overrides_) instance_params;
    decltype(cell_param_overrides_) cell_params;
    ScopeMap localparams;
    decltype(cell_liblist_bindings_) cell_liblist_bindings;
    decltype(config_delegations_) delegations;
    decltype(cell_config_delegations_) cell_delegations;
    std::string_view config;
  };
  std::vector<ConfigRuleTables> enclosing_config_rules_;
  std::string_view active_config_;

  std::string current_inst_path_;
  std::string config_inst_path_;
  std::string current_library_;
  bool in_config_elaboration_ = false;

  TypedefMap typedefs_;
  TypedefMap all_typedefs_;
  std::unordered_set<std::string_view> aggregate_typedef_names_;
  std::unordered_set<std::string_view> assoc_typedef_names_;
  std::unordered_map<std::string_view, uint32_t> fixed_unpacked_typedef_widths_;
  std::unordered_map<std::string_view, std::vector<Expr*>> td_array_dims_;
  std::unordered_set<std::string_view> cu_scope_names_;
  std::unordered_set<std::string_view> anonymous_program_names_;
  ScopeMap cu_param_scope_;
  ScopeMap all_cu_param_scope_;
  std::unordered_map<std::string_view, std::vector<Expr*>> all_td_array_dims_;

  ScopeMap replicate_multiplier_scope_;

  ScopeMap streaming_slice_size_scope_;

  ScopeMap array_query_dim_scope_;
  ScopeMap array_arg_dim_scope_;

  ScopeMap pla_ascending_scope_;

  ScopeMap procedural_typedef_scope_;
};

}  // namespace delta
