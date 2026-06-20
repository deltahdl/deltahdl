#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct PortDecl {
  Direction direction = Direction::kNone;
  DataType data_type;
  std::string_view name;
  std::vector<Expr*> unpacked_dims;
  Expr* default_value = nullptr;
  Expr* port_expr = nullptr;
  bool is_interface_port = false;
  bool is_explicit_named = false;
  bool has_explicit_var = false;
  SourceLoc loc;
};

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
};

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

struct GenerateCaseItem {
  std::vector<Expr*> patterns;
  bool is_default = false;
  std::vector<ModuleItem*> body;

  std::string_view label;
};

// §16.12.17 / §F.7: per-instance metadata for one named-property instantiation
// found in a property body. The recursive-property restrictions (Restriction 4
// in particular) inspect the actual argument expressions of each instance.
struct PropertyInstanceArgInfo {
  std::string_view callee;
  // One entry per actual argument, in declaration order. Each holds the set of
  // identifier tokens that appear textually within that argument expression.
  std::vector<std::vector<std::string_view>> arg_idents;
  // Parallel to arg_idents: true when the argument is a single bare identifier
  // (i.e. the actual argument expression is itself just one name).
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

struct ModuleItem {
  ModuleItemKind kind;
  SourceLoc loc;
  std::vector<Attribute> attrs;

  bool from_anonymous_program = false;

  bool is_automatic = false;
  bool is_static = false;

  bool is_extern = false;
  bool is_forkjoin = false;

  bool is_localparam = false;

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
  Expr* inst_range_left = nullptr;
  Expr* inst_range_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> inst_dims;

  DataType typedef_type;
  std::string_view typedef_ifc_port;
  std::string_view nettype_resolve_func;

  Stmt* gen_init = nullptr;
  Expr* gen_cond = nullptr;
  Stmt* gen_step = nullptr;
  std::vector<ModuleItem*> gen_body;
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
  bool is_ansi_ports = false;
  std::vector<FunctionArg> func_args;
  std::vector<Stmt*> func_body_stmts;

  std::vector<std::pair<Expr*, Expr*>> defparam_assigns;

  std::vector<Expr*> alias_nets;

  Expr* assert_expr = nullptr;
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  Expr* prop_body_expr = nullptr;

  // §16.12 / §F.4.1: metadata the rewriter needs to flatten property
  // instances and enforce the disable-iff no-nesting rule.
  std::vector<std::string_view> prop_formals;
  int prop_disable_iff_count = 0;
  std::vector<std::string_view> prop_instance_refs;

  // §16.12.17 / §F.7 recursive-property restriction metadata, harvested by the
  // parser body scan and enforced by the elaborator.
  //   prop_negated_instance_refs: names that are the operand of a prefix
  //     property-negation/strong operator (not, s_nexttime, s_eventually,
  //     s_always) or the right operand of s_until/s_until_with — Restriction 1.
  //   prop_formal_is_local: parallel to prop_formals; true when the formal was
  //     declared as a local variable formal argument — Restriction 4.
  //   prop_instance_args: actual-argument shape of each property instance in
  //     the body — Restriction 4.
  //   prop_has_untimed_self_recursion: a self-name instantiation occurs in the
  //     body with no preceding positive time advance — Restriction 3.
  std::vector<std::string_view> prop_negated_instance_refs;
  std::vector<bool> prop_formal_is_local;
  std::vector<PropertyInstanceArgInfo> prop_instance_args;
  bool prop_has_untimed_self_recursion = false;

  // §16.8.2: per-formal direction when the formal is designated as a local
  // variable argument. Length matches the number of local-marked formals in
  // declaration order; non-local formals are not represented here.
  std::vector<Direction> prop_seq_local_lvar_directions;

  // §16.10: identifiers introduced by assertion_variable_declaration items in
  // the body of a sequence or property declaration. Each entry is one local
  // variable declared in the body (a single declaration with N comma-
  // separated names produces N entries).
  std::vector<std::string_view> prop_seq_assert_vars;

  std::vector<EventExpr> clocking_event;
  std::vector<ClockingSignalDecl> clocking_signals;
  bool is_default_clocking = false;
  bool is_global_clocking = false;
  Edge default_input_skew_edge = Edge::kNone;
  Expr* default_input_skew_delay = nullptr;
  Edge default_output_skew_edge = Edge::kNone;
  Expr* default_output_skew_delay = nullptr;

  std::string_view dpi_c_name;
  // §35.5.4: the dpi_spec_string token, stripped of its surrounding quotes
  // ("DPI-C" or the deprecated "DPI").
  std::string_view dpi_spec_string;
  bool dpi_is_pure = false;
  bool dpi_is_context = false;
  bool dpi_is_task = false;

  ClassDecl* class_decl = nullptr;

  std::vector<SpecifyItem*> specify_items;

  ModuleDecl* nested_module_decl = nullptr;

  // §19.4.1: for the embedded-covergroup inheritance form
  // `covergroup extends base ;`, the covergroup_identifier of the base
  // covergroup being extended. Empty for a covergroup that is not derived.
  std::string_view covergroup_extends_base;
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
  std::string_view name;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::vector<PortDecl> ports;
  std::vector<ModuleItem*> items;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::vector<DataType> param_types;
  std::unordered_set<std::string_view> type_param_names;
  std::unordered_set<std::string_view> localparam_port_names;
  bool has_param_port_list = false;
  std::vector<ModportDecl*> modports;
  std::vector<BindDirective*> bind_directives;

  bool is_cell = false;

  std::string_view library;

  TimeUnit time_unit = TimeUnit::kNs;
  TimeUnit time_prec = TimeUnit::kNs;
  int time_unit_magnitude = 1;
  int time_prec_magnitude = 1;
  bool has_timeunit = false;
  bool has_timeprecision = false;
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
};

}  // namespace delta
