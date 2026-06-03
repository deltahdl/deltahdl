#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"

namespace delta {

struct Expr;
struct Stmt;
struct ModuleItem;
struct ModuleDecl;
struct SpecifyItem;
struct BindDirective;

enum class ExprKind : uint8_t {
  kIntegerLiteral,
  kRealLiteral,
  kTimeLiteral,
  kStringLiteral,
  kUnbasedUnsizedLiteral,
  kIdentifier,
  kSystemCall,
  kUnary,
  kBinary,
  kTernary,
  kConcatenation,
  kReplicate,
  kSelect,
  kMemberAccess,
  kCall,
  kAssignmentPattern,
  kCast,
  kTypeRef,
  kPostfixUnary,
  kInside,
  kStreamingConcat,
  kMinTypMax,
  kTagged,
};

struct Expr {
  ExprKind kind;
  SourceRange range;

  std::string_view text;
  std::string_view scope_prefix;
  uint64_t int_val = 0;
  double real_val = 0.0;

  TokenKind op = TokenKind::kEof;
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;

  Expr* condition = nullptr;
  Expr* true_expr = nullptr;
  Expr* false_expr = nullptr;

  std::string_view callee;
  std::vector<Expr*> args;
  std::vector<std::string_view> arg_names;

  Expr* base = nullptr;
  Expr* index = nullptr;
  Expr* index_end = nullptr;
  bool is_part_select_plus = false;
  bool is_part_select_minus = false;
  bool has_param_spec = false;

  Expr* with_expr = nullptr;
  bool with_has_parens = false;

  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;
  std::vector<std::string_view> pattern_keys;

  bool is_parenthesized = false;
};

// §11.5: an operand is "simple" iff it is not parenthesized AND is a primary
// (as defined in A.8.4). The example given is `1'b1 - 2'b00 + (1'b1 + 1'b1)`,
// where `1'b1 - 2'b00` (binary, not a primary) and `(1'b1 + 1'b1)`
// (parenthesized) are operands but not simple operands.
inline bool IsSimpleOperand(const Expr* e) {
  if (e == nullptr) return false;
  if (e->is_parenthesized) return false;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kIdentifier:
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kCast:
    case ExprKind::kStreamingConcat:
    case ExprKind::kTypeRef:
    case ExprKind::kTagged:
      return true;
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kTernary:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
    case ExprKind::kMinTypMax:
      return false;
  }
  return false;
}

struct Attribute {
  std::string_view name;
  Expr* value = nullptr;
  SourceLoc loc;
};

enum class Direction : uint8_t {
  kNone,
  kInput,
  kOutput,
  kInout,
  kRef,
};

enum class DataTypeKind : uint8_t {
  kImplicit,
  kLogic,
  kReg,
  kBit,
  kByte,
  kShortint,
  kInt,
  kLongint,
  kInteger,
  kReal,
  kShortreal,
  kTime,
  kRealtime,
  kString,
  kVoid,
  kNamed,
  kEnum,
  kStruct,
  kUnion,
  kEvent,
  kChandle,
  kWire,
  kTri,
  kWand,
  kWor,
  kTriand,
  kTrior,
  kTri0,
  kTri1,
  kTrireg,
  kSupply0,
  kSupply1,
  kUwire,
  kVirtualInterface,
};

struct EnumMember {
  std::string_view name;
  Expr* value = nullptr;
  Expr* range_start = nullptr;
  Expr* range_end = nullptr;
};

struct StructMember {
  DataTypeKind type_kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool is_rand = false;
  bool is_randc = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> extra_packed_dims;
  std::string_view name;
  std::string_view type_name;
  Expr* init_expr = nullptr;
  std::vector<Expr*> unpacked_dims;
  std::vector<Attribute> attrs;
};

struct DataType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool is_packed = false;
  bool is_const = false;
  bool is_net = false;
  bool is_interconnect = false;
  bool is_tagged = false;
  bool is_soft = false;
  bool is_vectored = false;
  bool is_scalared = false;
  uint8_t charge_strength = 0;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> extra_packed_dims;
  std::string_view type_name;
  std::string_view scope_name;
  std::string_view modport_name;
  std::string_view enum_base_name;

  DataTypeKind enum_base_kind = DataTypeKind::kImplicit;

  Expr* type_ref_expr = nullptr;
  std::vector<EnumMember> enum_members;
  std::vector<StructMember> struct_members;
  std::vector<DataType> type_params;
};

enum class StmtKind : uint8_t {
  kBlock,
  kIf,
  kCase,
  kFor,
  kForeach,
  kWhile,
  kForever,
  kRepeat,
  kDoWhile,
  kBreak,
  kContinue,
  kReturn,
  kBlockingAssign,
  kNonblockingAssign,
  kExprStmt,
  kTimingControl,
  kDelay,
  kEventControl,
  kWait,
  kWaitFork,
  kFork,
  kDisable,
  kDisableFork,
  kEventTrigger,
  kNbEventTrigger,
  kNull,
  kAssign,
  kDeassign,
  kForce,
  kRelease,
  kAssertImmediate,
  kAssumeImmediate,
  kCoverImmediate,
  kWaitOrder,
  kRandcase,
  kRandsequence,
  kVarDecl,
  kBlockItemDecl,
  kCycleDelay,
  kExpect,

};

enum class Edge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
  kEdge,
};

struct EventExpr {
  Edge edge = Edge::kNone;
  Expr* signal = nullptr;
  Expr* iff_condition = nullptr;
  bool is_sequence_event = false;
};

struct CaseItem {
  std::vector<Expr*> patterns;
  Stmt* body = nullptr;
  bool is_default = false;
};

enum class CaseQualifier : uint8_t {
  kNone,
  kUnique,
  kUnique0,
  kPriority,
};

enum class RsProdKind : uint8_t {
  kItem,
  kCodeBlock,
  kIf,
  kRepeat,
  kCase,
};

struct RsProductionItem {
  std::string_view name;
  std::vector<Expr*> args;
};

struct RsCaseItem {
  std::vector<Expr*> patterns;
  RsProductionItem item;
  bool is_default = false;
};

struct RsProd {
  RsProdKind kind = RsProdKind::kItem;
  RsProductionItem item;
  std::vector<Stmt*> code_stmts;
  Expr* condition = nullptr;
  RsProductionItem if_true;
  RsProductionItem if_false;
  bool has_else = false;
  Expr* repeat_count = nullptr;
  RsProductionItem repeat_item;
  Expr* case_expr = nullptr;
  std::vector<RsCaseItem> case_items;
};

struct RsRule {
  std::vector<RsProd> prods;
  bool is_rand_join = false;
  Expr* rand_join_expr = nullptr;
  std::vector<RsProductionItem> rand_join_items;
  Expr* weight = nullptr;
  std::vector<Stmt*> weight_code;
};

struct RsProduction {
  std::string_view name;
  bool has_return_type = false;
  bool has_ports = false;
  std::vector<RsRule> rules;
};

struct Stmt {
  StmtKind kind;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::string_view label;
  CaseQualifier qualifier = CaseQualifier::kNone;

  std::vector<Stmt*> stmts;

  Expr* condition = nullptr;
  Stmt* then_branch = nullptr;
  Stmt* else_branch = nullptr;

  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  Expr* delay = nullptr;
  Expr* cycle_delay = nullptr;

  std::vector<Stmt*> for_inits;
  Expr* for_cond = nullptr;
  std::vector<Stmt*> for_steps;
  Stmt* for_body = nullptr;
  std::vector<DataType> for_init_types;

  std::vector<CaseItem> case_items;
  TokenKind case_kind = TokenKind::kKwCase;
  bool case_inside = false;
  bool case_matches = false;

  std::vector<EventExpr> events;
  bool is_star_event = false;
  Expr* repeat_event_count = nullptr;

  std::vector<Stmt*> fork_stmts;
  TokenKind join_kind = TokenKind::kKwJoin;

  Expr* expr = nullptr;

  Stmt* body = nullptr;

  std::vector<std::string_view> foreach_vars;

  Expr* assert_expr = nullptr;
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  bool is_deferred = false;

  bool is_final_deferred = false;

  bool is_procedural_concurrent = false;

  std::vector<Expr*> wait_order_events;

  std::vector<std::pair<Expr*, Stmt*>> randcase_items;

  std::string_view rs_top_production;
  std::vector<RsProduction> rs_productions;

  DataType var_decl_type;
  std::string_view var_name;
  std::vector<Expr*> var_unpacked_dims;
  Expr* var_init = nullptr;
  bool var_is_automatic = false;
  bool var_is_static = false;
  bool var_is_const = false;

  ModuleItem* decl_item = nullptr;
};

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

struct FunctionArg {
  Direction direction = Direction::kNone;
  bool is_const = false;
  bool is_ref_static = false;
  bool is_default = false;
  DataType data_type;
  std::string_view name;
  Expr* default_value = nullptr;
  std::vector<Expr*> unpacked_dims;
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

enum class ClassMemberKind : uint8_t {
  kProperty,
  kMethod,
  kConstraint,
  kTypedef,
  kClassDecl,
  kCovergroup,
};

// 18.5.7.1: a foreach iterative constraint as seen in a constraint block body.
// array_name is the (trailing) identifier of the iterated array; loop_var_count
// is the number of loop variables given, counted up to the last nonempty slot
// so a trailing run of omittable commas does not inflate it. loc points at the
// foreach for diagnostics. The parser records these from the constraint body so
// the elaborator — which can resolve the array's declaration and therefore its
// dimensionality — can enforce that the loop-variable count does not exceed the
// array's number of dimensions.
struct ConstraintForeachRef {
  std::string_view array_name;
  int loop_var_count = 0;
  SourceLoc loc;
};

// 18.5.9: one constraint_primary appearing in a solve...before list. 'name' is
// the trailing (leaf) identifier of the reference. is_simple marks a bare local
// identifier — no class_scope/implicit_class_handle qualifier and no trailing
// '()' array-method call (such as size()). The elaborator only applies the
// solve...before variable restrictions (must be rand, not randc, integral or
// real) to simple entries it can resolve to a class property; a qualified or
// array-method primary is left alone, since array.size() is expressly allowed as
// an ordering variable.
struct ConstraintSolveBeforeEntry {
  std::string_view name;
  bool is_simple = true;
};

// 18.5.9: a 'solve solve_before_list before solve_before_list ;' ordering
// constraint as seen in a constraint block body. 'before' holds the variables to
// be solved first; 'after' holds those solved afterward. loc points at the solve
// keyword for diagnostics. The parser records these so the elaborator can enforce
// the variable-ordering restrictions and reject circular dependencies.
struct ConstraintSolveBeforeRef {
  std::vector<ConstraintSolveBeforeEntry> before;
  std::vector<ConstraintSolveBeforeEntry> after;
  SourceLoc loc;
};

struct ClassMember {
  ClassMemberKind kind = ClassMemberKind::kProperty;
  SourceLoc loc;

  bool is_static = false;
  bool is_virtual = false;
  bool is_local = false;
  bool is_protected = false;
  bool is_rand = false;
  bool is_randc = false;
  bool is_const = false;
  bool is_pure_virtual = false;

  bool is_constraint_initial = false;
  bool is_constraint_extends = false;
  bool is_constraint_final = false;

  // 18.5.1: a constraint declared without a body is a constraint prototype that
  // is completed by an external constraint block. The explicit prototype form
  // uses the 'extern' keyword; the implicit form omits it.
  bool is_constraint_prototype = false;
  bool is_constraint_extern = false;

  // 18.5.7.1: the foreach iterative constraints found in this constraint
  // block's body (empty for non-constraint members).
  std::vector<ConstraintForeachRef> constraint_foreach_refs;

  // 18.5.9: the solve...before ordering constraints found in this constraint
  // block's body (empty for non-constraint members).
  std::vector<ConstraintSolveBeforeRef> constraint_solve_before_refs;

  DataType data_type;
  std::string_view name;
  std::vector<Expr*> unpacked_dims;
  Expr* init_expr = nullptr;

  ModuleItem* method = nullptr;
  ModuleItem* typedef_item = nullptr;

  ClassDecl* nested_class = nullptr;

  // §19.4.1: when this member is a derived covergroup declared with the
  // embedded inheritance form `covergroup extends base ;`, the
  // covergroup_identifier of the base covergroup. Empty otherwise.
  std::string_view covergroup_extends_base;
};

struct InterfaceRef {
  std::string_view name;
  std::vector<DataType> type_params;
};

struct ClassDecl {
  std::string_view name;
  SourceRange range;
  bool is_virtual = false;
  bool is_final = false;
  bool is_interface = false;
  std::string_view base_class;
  std::vector<DataType> base_class_type_params;
  std::vector<Expr*> extends_args;
  bool extends_has_default = false;
  std::vector<InterfaceRef> extends_interfaces;
  std::vector<InterfaceRef> implements_types;
  std::vector<ClassMember*> members;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::unordered_set<std::string_view> type_param_names;
  std::unordered_set<std::string_view> localparam_port_names;
};

enum class SpecifyPathKind : uint8_t {
  kParallel,
  kFull,
};

enum class SpecifyEdge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
  kEdge,
};

enum class SpecifyPolarity : uint8_t {
  kNone,
  kPositive,
  kNegative,
};

enum class SpecifyRangeKind : uint8_t {
  kNone,
  kBitSelect,
  kPartSelect,
  kPlusIndexed,
  kMinusIndexed,
};

struct SpecifyTerminal {
  std::string_view name;
  std::string_view interface_name;
  Expr* range_left = nullptr;
  Expr* range_right = nullptr;
  SpecifyRangeKind range_kind = SpecifyRangeKind::kNone;
};

struct SpecifyPathDecl {
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;
  SpecifyPolarity polarity = SpecifyPolarity::kNone;
  SpecifyPolarity dst_polarity = SpecifyPolarity::kNone;
  std::vector<SpecifyTerminal> src_ports;
  std::vector<SpecifyTerminal> dst_ports;
  std::vector<Expr*> delays;
  Expr* condition = nullptr;
  Expr* data_source = nullptr;
  bool is_ifnone = false;
  SourceLoc loc;
};

enum class TimingCheckKind : uint8_t {
  kSetup,
  kHold,
  kSetuphold,
  kRecovery,
  kRemoval,
  kRecrem,
  kWidth,
  kPeriod,
  kSkew,
  kNochange,
  kTimeskew,
  kFullskew,
};

inline bool IsStabilityWindowTimingCheck(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
      return true;
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kSkew:
    case TimingCheckKind::kNochange:
    case TimingCheckKind::kTimeskew:
    case TimingCheckKind::kFullskew:
      return false;
  }
  return false;
}

inline bool IsClockControlTimingCheck(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSkew:
    case TimingCheckKind::kTimeskew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kNochange:
      return true;
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
      return false;
  }
  return false;
}

struct TimingCheckDecl {
  TimingCheckKind check_kind = TimingCheckKind::kSetup;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  SpecifyTerminal ref_terminal;
  Expr* ref_condition = nullptr;
  std::vector<std::pair<char, char>> ref_edge_descriptors;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  SpecifyTerminal data_terminal;
  Expr* data_condition = nullptr;
  std::vector<std::pair<char, char>> data_edge_descriptors;
  std::vector<Expr*> limits;
  std::string_view notifier;

  Expr* timestamp_cond = nullptr;
  Expr* timecheck_cond = nullptr;
  std::string_view delayed_ref;
  Expr* delayed_ref_expr = nullptr;
  std::string_view delayed_data;
  Expr* delayed_data_expr = nullptr;

  Expr* event_based_flag = nullptr;
  Expr* remain_active_flag = nullptr;
  SourceLoc loc;
};

enum class SpecifyItemKind : uint8_t {
  kPathDecl,
  kTimingCheck,
  kPulsestyle,
  kShowcancelled,
  kSpecparam,
};

struct SpecifyItem {
  SpecifyItemKind kind = SpecifyItemKind::kPathDecl;
  SourceLoc loc;

  SpecifyPathDecl path;

  TimingCheckDecl timing_check;

  bool is_ondetect = false;
  bool is_noshowcancelled = false;
  std::vector<std::string_view> signal_list;

  std::string_view param_name;
  Expr* param_value = nullptr;

  bool is_pathpulse = false;
  std::string_view pathpulse_input;
  std::string_view pathpulse_output;
  Expr* pathpulse_reject = nullptr;
  Expr* pathpulse_error = nullptr;
};

struct UdpTableRow {
  std::vector<char> inputs;

  std::vector<std::pair<char, char>> paren_edges;
  char current_state = 0;
  char output = '0';
};

struct UdpDecl {
  std::string_view name;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::string_view output_name;
  std::vector<std::string_view> input_names;
  bool is_sequential = false;
  bool has_initial = false;
  char initial_value = 'x';
  std::vector<UdpTableRow> table;
  std::string_view library;
};

struct LibraryDecl {
  std::string_view name;
  std::vector<std::string_view> file_paths;
  std::vector<std::string_view> incdir_paths;
  SourceRange range;
};

struct IncludeStmt {
  std::string_view file_path;
  SourceLoc loc;
};

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
