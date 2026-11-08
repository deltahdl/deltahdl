#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir_alias.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_checker_site.h"
#include "elaborator/rtlir_defparam.h"
#include "elaborator/rtlir_element_shape.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_io_decl.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/rtlir_typedef_facts.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_fsm.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

enum class RtlirProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
  kFinal,
};

struct RtlirUnpackedDim {
  int64_t left = 0;
  int64_t right = 0;

  [[nodiscard]] int64_t Low() const { return left < right ? left : right; }

  [[nodiscard]] uint32_t Size() const {
    return static_cast<uint32_t>((left < right ? right - left : left - right) +
                                 1);
  }
};

struct RtlirPort {
  std::string_view name;
  Direction direction;
  DataTypeKind type_kind;
  DataTypeKind data_kind = DataTypeKind::kImplicit;
  uint32_t width = 1;
  bool is_signed = false;

  const DataType* dtype = nullptr;

  bool is_var = false;
  bool elem_type_is_unpacked_array = false;
  NetType net_type = NetType::kNone;
  bool is_interconnect = false;
  bool is_interface_port = false;
  bool is_explicit_named = false;
  std::string_view interface_type_name;
  Expr* default_value = nullptr;
  Expr* init_value = nullptr;
  Expr* port_expr = nullptr;
  uint32_t selected_width = 0;
  std::vector<ResolvedAttribute> attrs;
  uint32_t num_unpacked_dims = 0;
  std::vector<uint32_t> unpacked_dim_sizes;
  std::vector<RtlirUnpackedDim> unpacked_dims;
  bool type_is_array = false;
  const DataType* declared_type = nullptr;
  SourceLoc loc;
};

struct RtlirNet {
  std::string_view name;
  NetType net_type = NetType::kWire;
  uint32_t width = 1;

  const DataType* dtype = nullptr;

  uint32_t num_unpacked_dims = 0;
  std::vector<uint32_t> unpacked_dim_sizes;
  std::vector<RtlirUnpackedDim> unpacked_dims;

  bool is_signed = false;
  std::vector<uint32_t> driver_indices;
  DataTypeKind data_kind = DataTypeKind::kImplicit;
  bool has_declared_packed_dim = false;
  const DataType* written_type = nullptr;
  const std::vector<Expr*>* declared_unpacked_dims = nullptr;

  Strength charge_strength = Strength::kMedium;
  uint32_t trireg_capacitance = 0;

  uint64_t decay_ticks = 0;
  bool decay_is_real = false;
  double decay_real = 0.0;

  bool decays = false;

  Expr* delay_rise = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_turnoff = nullptr;

  bool is_vectored = false;
  bool is_scalared = false;

  bool is_user_nettype = false;
  std::string_view resolve_func;

  std::string_view nettype_name;
  std::vector<ResolvedAttribute> attrs;

  SourceLoc loc;
  SourceLoc implicit_ref_loc;

  bool refers_outward = false;
};

struct RtlirVariable {
  std::string_view name;
  bool is_enum_constant = false;
  uint32_t width = 1;
  bool is_4state = true;
  bool is_event = false;
  bool is_string = false;
  bool is_real = false;
  bool is_signed = false;
  bool is_chandle = false;
  const Expr* init_expr = nullptr;
  GenBlockConsts gen_block_consts;
  const DataType* dtype = nullptr;
  const DataType* written_type = nullptr;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  DataTypeKind decl_kind = DataTypeKind::kImplicit;
  uint32_t unpacked_size = 0;
  int64_t unpacked_lo = 0;
  bool is_descending = false;
  std::vector<uint32_t> unpacked_dim_sizes;
  std::vector<RtlirUnpackedDim> unpacked_dims;
  uint32_t num_unpacked_dims = 0;
  const std::vector<Expr*>* declared_unpacked_dims = nullptr;
  bool is_dynamic = false;
  bool is_queue = false;
  int32_t queue_max_size = -1;
  bool elements_are_queues = false;
  RtlirElementShape element;
  bool is_assoc = false;
  bool is_string_index = false;
  bool is_wildcard_index = false;
  bool is_class_index = false;
  bool is_index_signed = true;
  uint32_t assoc_index_width = 32;
  std::string_view assoc_index_keyword;
  std::string_view assoc_index_class_name;
  std::string_view assoc_index_type_name;
  std::string_view class_type_name;
  const DataType* class_data_type = nullptr;
  const CovergroupDecl* covergroup = nullptr;
  std::string_view enum_type_name;
  std::vector<ResolvedAttribute> attrs;

  SourceLoc loc;
  std::string_view gen_block_prefix;
};

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  const ModuleItem* source_item = nullptr;
  uint32_t width = 0;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;
  bool from_nonresistive_switch = false;
  bool from_resistive_switch = false;
  Expr* data_input = nullptr;

  Expr* three_state_ctrl = nullptr;
  Expr* three_state_pass = nullptr;
  std::string interconnect_load;
  std::string interconnect_source;
  std::string module_path_port;
  std::vector<ResolvedAttribute> attrs;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
  HierPath gen_block_path;
};

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  bool is_static_assertion = false;
  std::vector<ProceduralCheckerSite> checker_instances;
  bool is_concurrent_clocked = false;
  SourceLoc loc;
  std::vector<EventExpr> gclk_future_event;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
  HierPath gen_block_path;
};

struct RtlirParamDecl {
  std::string_view name;
  SourceLoc loc;
  std::string_view gen_block_prefix;
  Expr* default_value = nullptr;
  const std::vector<Expr*>* unpacked_dims = nullptr;
  std::vector<RtlirUnpackedDim> unpacked_bounds;
  const Expr* override_expr = nullptr;
  int64_t resolved_value = 0;
  std::vector<uint64_t> resolved_high_words;
  uint32_t value_width = 0;
  bool value_is_signed = false;
  double resolved_real = 0.0;
  bool is_real_value = false;
  bool decl_is_real = false;
  std::string_view resolved_string;
  bool is_string_value = false;
  bool is_resolved = false;
  bool is_localparam = false;
  bool from_override = false;
  bool is_unbounded = false;
  bool is_type_param = false;
  bool config_locked = false;

  uint32_t decl_width = 0;
  bool decl_is_signed = false;
  bool has_decl_type = false;
  bool has_decl_range = false;
  int64_t decl_range_left = 0;
  int64_t decl_range_right = 0;
  bool has_decl_range_bounds = false;
  bool decl_type_implicit = false;
  const DataType* decl_type = nullptr;
  const DataType* resolved_type = nullptr;
  const Expr* defparam_value_expr = nullptr;
  std::unordered_map<std::string_view, int64_t> defparam_value_scope;
  GenBlockPrefixes defparam_value_scopes;
  const struct RtlirModule* defparam_module = nullptr;
  std::unordered_map<std::string_view, int64_t> override_scope;
  const struct RtlirModule* override_module = nullptr;
  const DataType* type_param_actual = nullptr;
  bool decl_is_shortreal = false;
  const struct ParamDefaultMismatch* default_mismatch = nullptr;
};

struct RtlirPortBinding {
  std::string_view port_name;
  Direction direction;
  Expr* connection = nullptr;
  uint32_t width = 1;
  Expr* port_expr = nullptr;
  bool unconnected = false;
  bool refused_actual = false;
  bool uwire_net_join = false;
};

struct RtlirModuleInst {
  std::string_view module_name;
  std::string_view inst_name;
  std::string_view simple_inst_name;
  HierPath gen_block_path;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
  struct RtlirModule* resolved = nullptr;
  std::vector<RtlirPortBinding> port_bindings;
  std::vector<ResolvedAttribute> attrs;
  bool is_bound = false;
  bool ports_by_name = false;
  InstArrayElement array;
  bool is_nested_decl = false;
  bool is_procedural = false;
  std::vector<std::string_view> procedure_locals;
  std::vector<std::string_view> procedure_automatics;
};

struct TypeRefCompareResult {
  const Expr* expr = nullptr;
  std::string_view gen_prefix;
  bool holds = false;
};

struct RtlirModule {
  std::string_view name;
  SourceLoc loc;

  std::string_view library;
  std::string_view config;
  int unit_index = -1;
  bool has_param_port_list = false;
  bool is_program = false;
  bool is_interface = false;
  bool is_checker = false;
  bool is_automatic = false;
  std::vector<ResolvedAttribute> attrs;
  RtlirNodeAttributes node_attrs;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;
  uint64_t default_decay_time = 0;
  bool default_decay_time_infinite = true;
  bool default_decay_time_is_real = false;
  double default_decay_time_real = 0.0;
  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  TimeScale timescale;

  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;

  std::vector<RtlirPort> ports;
  std::vector<RtlirNet> nets;
  std::vector<RtlirVariable> variables;
  std::vector<RtlirContAssign> assigns;
  std::vector<RtlirUdpInst> udp_insts;
  std::vector<RtlirAlias> aliases;
  std::vector<RtlirDefparam> defparams;
  std::vector<RtlirIoDecl> port_expr_decls;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  std::vector<RtlirBlockParamOverride> block_param_overrides;
  std::vector<FsmDecl> fsms;
  std::vector<ModuleItem*> clocking_blocks;
  std::vector<RtlirAssertion> assertions;
  std::vector<RtlirAssertionItemDecl> assertion_item_decls;
  std::vector<const ModportDecl*> modports;
  Expr* default_disable_iff = nullptr;
  std::vector<EventExpr> inherited_default_clock;
  std::vector<std::pair<std::string_view, int64_t>> constant_formals;
  std::vector<std::string_view> free_variables;
  std::vector<std::string_view> random_initial_variables;
  std::vector<ModuleItem*> function_decls;
  std::vector<RtlirGenBlockSubroutine> gen_block_subroutines;
  std::vector<RtlirGenBlockMember> gen_block_members;
  std::vector<HierPath> gen_block_instances;
  std::vector<RtlirGenBlockClocking> gen_block_clocking;
  std::vector<RtlirGenBlockTypedef> gen_block_typedefs;
  std::vector<RtlirGenBlockClass> gen_block_classes;
  std::vector<ModuleItem*> let_decls;
  std::vector<RtlirGenBlockLet> gen_block_lets;
  std::vector<ModuleItem*> dpi_import_decls;
  std::vector<ModuleItem*> dpi_export_decls;
  std::vector<ModuleItem*> specify_blocks;
  std::vector<ModuleItem*> gate_insts;
  std::vector<RtlirBidirSwitch> bidir_switches;
  std::vector<std::string_view> specparam_names;
  std::vector<ModuleItem*> sequence_decls;
  std::vector<ModuleItem*> property_decls;
  std::vector<ClassDecl*> class_decls;
  std::vector<RtlirImport> imports;

  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enum_types;
  const ModuleDecl* decl = nullptr;
  std::vector<TypeRefCompareResult> type_ref_compares;
};

struct RtlirDesign : RtlirTypedefFacts {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;

  std::unordered_map<std::string_view, int64_t> unit_constants;

  const CompilationUnit* compilation_unit = nullptr;
  std::vector<CompilationUnit*> compilation_units;
  std::vector<const ModuleDecl*> top_decls;

  std::vector<ModuleItem*> cu_function_decls;

  std::vector<ModuleItem*> cu_let_decls;

  std::vector<PackageDecl*> packages;

  std::vector<ClassDecl*> cu_class_decls;
  RtlirNodeAttributes node_attrs;

  TimeScale cu_timescale;

  TimeUnit global_time_precision = TimeUnit::kNs;
  int global_precision_order = -9;

  bool simulation_blocked = false;

  std::string last_elab_severity;
  std::string last_elab_severity_msg;
  std::string last_elab_severity_scope;
  SourceLoc last_elab_severity_loc;
  std::vector<TypeRefCompareResult> unit_type_ref_compares;
};

}  // namespace delta
