#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_assertion_text.h"
#include "parser/ast_expr.h"
#include "parser/ast_fsm.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

enum class PropertyFormalType : uint8_t {
  kData,
  kSequence,
  kUntyped,
  kProperty
};

struct PortDecl {
  Direction direction = Direction::kNone;
  DataType data_type;
  PropertyFormalType formal_type = PropertyFormalType::kData;
  std::string_view name;
  std::vector<Expr*> unpacked_dims;
  Expr* default_value = nullptr;
  Expr* port_expr = nullptr;
  bool is_interface_port = false;
  bool is_explicit_named = false;
  bool has_explicit_var = false;
  SourceLoc loc;
  std::vector<Attribute> attrs;
};

enum class InferredDefault : uint8_t { kNone, kClock, kDisable };

enum class ModuleItemKind : uint8_t {
  kNetDecl,
  kVarDecl,
  kParamDecl,
  kContAssign,
  kInitialBlock,
  kFinalBlock,
  kAlwaysBlock,
  kAlwaysCombBlock,
  kAlwaysFFBlock,
  kAlwaysLatchBlock,
  kGenerateFor,
  kGenerateIf,
  kGenerateCase,
  kModuleInst,
  kTypedef,
  kFunctionDecl,
  kTaskDecl,
  kImportDecl,
  kExportDecl,
  kGateInst,
  kUdpInst,
  kDefparam,
  kAlias,
  kPropertyDecl,
  kSequenceDecl,
  kAssertProperty,
  kAssumeProperty,
  kCoverProperty,
  kCoverSequence,
  kRestrictProperty,
  kClockingBlock,
  kCovergroupDecl,
  kSpecifyBlock,
  kSpecparam,
  kDpiImport,
  kDpiExport,
  kClassDecl,
  kNettypeDecl,
  kLetDecl,
  kElabSystemTask,
  kDefaultDisableIff,
  kNestedModuleDecl,
  kBindDirective,
};

inline bool IsProceduralItemKind(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kInitialBlock:
    case ModuleItemKind::kFinalBlock:
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      return true;
    default:
      return false;
  }
}

enum class GateKind : uint8_t {

  kAnd,
  kNand,
  kOr,
  kNor,
  kXor,
  kXnor,

  kBuf,
  kNot,

  kBufif0,
  kBufif1,
  kNotif0,
  kNotif1,

  kTran,
  kRtran,

  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,

  kNmos,
  kPmos,
  kRnmos,
  kRpmos,

  kCmos,
  kRcmos,

  kPullup,
  kPulldown,
};

enum class AlwaysKind : uint8_t {
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
};

struct ImportItem {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
  bool is_header = false;
};

struct ModuleItem;
struct ClassDecl;
struct CovergroupDecl;

struct GenerateCaseItem {
  std::vector<Expr*> patterns;
  bool is_default = false;
  std::vector<ModuleItem*> body;

  bool name_is_generated = false;

  bool has_begin_end = false;

  std::string_view label;
};

struct PropertyInstanceArgInfo {
  std::string_view callee;
  std::vector<std::vector<std::string_view>> arg_idents;
  std::vector<bool> arg_is_single_ident;
};

struct ClockingSignalDecl {
  Direction direction = Direction::kNone;
  Edge skew_edge = Edge::kNone;
  Expr* skew_delay = nullptr;
  Edge out_skew_edge = Edge::kNone;
  Expr* out_skew_delay = nullptr;
  std::string_view name;
  Expr* hier_expr = nullptr;
};

struct SeqCycleDelay {
  static constexpr uint32_t kUnbounded = UINT32_MAX;
  uint32_t min = 1;
  uint32_t max = 1;
  Expr* min_expr = nullptr;
  Expr* max_expr = nullptr;
  bool written = false;
};

struct SeqMatchAssign {
  std::string_view lvar;
  TokenKind op = TokenKind::kEq;
  Expr* rhs = nullptr;
  bool init = false;
  bool on_empty_match = false;
  Expr* call = nullptr;
  Expr* target = nullptr;
};

struct SeqLocalDecl {
  std::string_view name;
  TokenKind type_kw = TokenKind::kKwInt;
  TokenKind signing = TokenKind::kEof;
  DataType named_type;
  std::vector<std::pair<Expr*, Expr*>> packed_dims;
  Expr* init = nullptr;
};

struct SeqRepetition : SeqCycleDelay {
  enum class Kind : uint8_t { kNone, kConsecutive, kGoto, kNonconsecutive };
  Kind kind = Kind::kNone;
  bool IteratesWhole() const {
    return kind == Kind::kConsecutive &&
           (min != max || min == 0 || max_expr != nullptr);
  }
};

struct SeqThroughout {
  Expr* cond = nullptr;
  size_t first = 0;
  size_t last = 0;
  uint32_t lead = 0;
  bool begins_at_read = false;
};

struct SeqLinearBody {
  std::vector<Expr*> operands;
  std::vector<SeqCycleDelay> delays;
  std::vector<std::vector<SeqMatchAssign>> match_items;
  std::vector<SeqRepetition> repetitions;
  std::vector<SeqLocalDecl> locals;
  std::vector<SeqThroughout> throughouts;
  std::vector<SeqLinearBody> intersects;
  bool within = false;
  std::vector<SeqLinearBody> conjuncts;
  std::vector<SeqLinearBody> alternatives;
  bool first_match = false;
  std::vector<SeqMatchAssign> first_match_items;
  std::vector<std::vector<EventExpr>> clocks;
  std::vector<EventExpr> clock_out;
};

struct ModuleItem {
  ModuleItemKind kind;
  SourceLoc loc;
  SourceLoc end;
  std::vector<Attribute> attrs;

  bool from_anonymous_program = false;

  bool is_automatic = false;
  bool is_static = false;
  bool is_static_method = false;

  bool is_extern = false;
  bool is_forkjoin = false;

  bool is_localparam = false;

  bool first_in_decl_list = true;
  bool has_explicit_var = false;
  std::string_view fsm_enum;

  bool is_genvar = false;

  bool type_name_undeclared_at_parse = false;

  bool udp_undeclared_at_parse = false;

  DataTypeKind forward_type_kind = DataTypeKind::kImplicit;

  bool is_rand = false;

  bool is_method_initial = false;
  bool is_method_extends = false;
  bool is_method_final = false;

  std::string_view method_class;

  DataType data_type;
  std::string_view name;
  Expr* init_expr = nullptr;
  std::vector<Expr*> unpacked_dims;

  Expr* assign_lhs = nullptr;
  Expr* assign_rhs = nullptr;
  Expr* assign_delay = nullptr;
  Expr* assign_delay_fall = nullptr;
  Expr* assign_delay_decay = nullptr;

  Expr* net_delay = nullptr;
  Expr* net_delay_fall = nullptr;
  Expr* net_delay_decay = nullptr;

  AlwaysKind always_kind = AlwaysKind::kAlways;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;

  std::string_view inst_scope;
  std::string_view inst_module;
  std::string_view inst_name;
  std::vector<std::pair<std::string_view, Expr*>> inst_params;
  std::vector<std::pair<std::string_view, Expr*>> inst_ports;
  std::vector<bool> inst_ports_implicit;
  bool inst_wildcard = false;
  bool inst_continues_list = false;
  bool inst_in_procedure = false;
  Expr* inst_range_left = nullptr;
  Expr* inst_range_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> inst_dims;

  DataType typedef_type;
  std::string_view typedef_ifc_port;
  std::string_view nettype_resolve_func;
  const DataType* nettype_resolve_scope = nullptr;

  Stmt* gen_init = nullptr;
  Expr* gen_cond = nullptr;
  Stmt* gen_step = nullptr;
  std::vector<ModuleItem*> gen_body;
  bool gen_body_has_begin_end = false;

  bool name_is_generated = false;
  ModuleItem* gen_else = nullptr;
  std::vector<GenerateCaseItem> gen_case_items;

  ImportItem import_item;

  GateKind gate_kind = GateKind::kAnd;
  std::string_view gate_inst_name;
  std::vector<Expr*> gate_terminals;
  Expr* gate_delay = nullptr;
  Expr* gate_delay_fall = nullptr;
  Expr* gate_delay_decay = nullptr;

  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;

  DataType return_type;
  std::vector<Expr*> return_array_dims;
  DataType return_array_elem_type;
  bool is_ansi_ports = false;
  std::vector<FunctionArg> func_args;
  std::vector<Stmt*> func_body_stmts;
  const ModuleItem* out_of_block_body = nullptr;

  std::vector<std::pair<Expr*, Expr*>> defparam_assigns;

  std::vector<Expr*> alias_nets;

  Expr* assert_expr = nullptr;
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  std::string_view prop_instance_name;
  std::vector<EventExpr> prop_clock;
  Expr* prop_body_expr = nullptr;
  Expr* prop_disable_iff = nullptr;
  bool prop_negated = false;
  PropertyExprNode* prop_body_tree = nullptr;
  std::vector<SeqLocalDecl> prop_locals;

  std::vector<std::string_view> prop_formals;
  int prop_disable_iff_count = 0;
  std::vector<std::string_view> prop_instance_refs;

  std::vector<std::string_view> prop_negated_instance_refs;
  std::vector<std::string_view> prop_untimed_instance_refs;
  std::vector<bool> prop_formal_is_local;
  std::vector<bool> prop_formal_is_property;
  std::vector<PropertyInstanceArgInfo> prop_instance_args;
  bool prop_has_untimed_self_recursion = false;

  std::vector<Direction> prop_seq_local_lvar_directions;

  std::vector<bool> prop_formal_has_default;
  std::vector<Expr*> prop_formal_defaults;
  std::vector<InferredDefault> prop_formal_inferred;

  std::vector<TokenKind> prop_formal_type_kw;
  std::vector<DataType*> prop_formal_types;
  std::vector<std::vector<Expr*>> prop_formal_unpacked_dims;

  std::vector<std::string_view> prop_seq_assert_vars;

  std::vector<AssertionRead> assertion_reads;
  std::vector<std::string_view> assertion_local_names;
  std::vector<std::string_view> assertion_const_names;
  std::vector<AssertionInstanceArg> assertion_instance_args;

  std::vector<EventExpr> clocking_event;

  std::vector<EventExpr> seq_clock;
  SeqLinearBody seq_linear;
  bool seq_triggered_unread = false;

  bool decl_has_leading_clock = false;

  int decl_clock_event_count = 0;

  std::vector<ClockingSignalDecl> clocking_signals;
  std::vector<ModuleItem*> clocking_decls;
  bool is_default_clocking = false;
  bool is_global_clocking = false;
  Edge default_input_skew_edge = Edge::kNone;
  Expr* default_input_skew_delay = nullptr;
  Edge default_output_skew_edge = Edge::kNone;
  Expr* default_output_skew_delay = nullptr;

  std::string_view dpi_c_name;
  std::string_view dpi_spec_string;
  bool dpi_is_pure = false;
  bool dpi_is_context = false;
  bool dpi_is_task = false;

  ClassDecl* class_decl = nullptr;

  std::vector<SpecifyItem*> specify_items;

  ModuleDecl* nested_module_decl = nullptr;

  BindDirective* bind_directive = nullptr;

  std::string_view covergroup_extends_base;

  CovergroupDecl* covergroup = nullptr;

  bool inst_param_assignment_written = false;

  SourceLoc inst_port_attr_loc;
};

enum class ModuleDeclKind : uint8_t {
  kModule,
  kInterface,
  kProgram,
  kChecker,
};

struct ModportPort {
  Direction direction = Direction::kNone;
  std::string_view name;
  Expr* expr = nullptr;
  bool is_import = false;
  bool is_export = false;
  bool is_clocking = false;
  bool is_named_port = false;
  ModuleItem* prototype = nullptr;
};

struct ModportDecl {
  std::string_view name;
  std::vector<ModportPort> ports;
  SourceLoc loc;
};

struct ModuleDecl {
  ModuleDeclKind decl_kind = ModuleDeclKind::kModule;
  bool is_extern = false;
  bool is_automatic = false;
  bool has_wildcard_ports = false;
  bool is_non_ansi_ports = false;
  bool has_read_body_item = false;
  std::string_view name;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::vector<PortDecl> ports;
  std::vector<PortDecl> port_expr_objects;
  std::vector<ModuleItem*> items;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::vector<DataType> param_types;
  std::vector<SourceLoc> param_port_locs;
  std::unordered_map<std::string_view, std::vector<Expr*>>
      param_port_unpacked_dims;
  std::unordered_set<std::string_view> type_param_names;
  std::unordered_set<std::string_view> localparam_port_names;
  bool has_param_port_list = false;
  std::vector<ModportDecl*> modports;
  std::vector<BindDirective*> bind_directives;
  std::vector<FsmDecl> fsms;

  bool is_cell = false;

  bool has_module_directives = false;
  uint64_t default_decay_time = 0;
  bool default_decay_time_infinite = true;
  bool default_decay_time_is_real = false;
  double default_decay_time_real = 0.0;
  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;

  std::string_view library;

  TimeUnit time_unit = TimeUnit::kNs;
  TimeUnit time_prec = TimeUnit::kNs;
  int time_unit_magnitude = 1;
  int time_prec_magnitude = 1;
  bool has_timeunit = false;
  bool has_timeprecision = false;
  bool has_directive_timescale = false;
  TimeScale directive_timescale;
  bool has_net_directives = false;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;
};

struct PackageDecl {
  std::string_view name;
  SourceRange range;
  std::vector<ModuleItem*> items;
  std::string_view library;
  TimeUnit time_unit = TimeUnit::kNs;
  TimeUnit time_prec = TimeUnit::kNs;
  int time_unit_magnitude = 1;
  int time_prec_magnitude = 1;
  bool has_timeunit = false;
  bool has_timeprecision = false;
  bool is_automatic = false;
  bool has_directive_timescale = false;
  TimeScale directive_timescale;
  bool has_read_body_item = false;
};

}  // namespace delta
