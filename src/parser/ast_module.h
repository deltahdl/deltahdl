#pragma once

#include <cstddef>
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

// The keyword forms of A.1.8's property_formal_type, which A.2.10 spells
// `sequence_formal_type | property` with `sequence_formal_type ::=
// data_type_or_implicit | sequence | untyped`. A checker formal written with
// a data type, or with none, is kData and carries the type in its data_type;
// one written with one of the three keywords carries the keyword here. §17.2
// has the first formal of a checker "assumed to be input untyped" when its
// type is omitted, so a checker's first formal with no type is kUntyped.
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
};

// §16.14.7: the inferred clocking or disable function a formal argument of a
// property or sequence is defaulted to, where it is one.
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
};

// Whether `kind` is a module item whose body is a procedural statement. §9.2
// lists the structured procedures: the `initial` procedure of §9.2.1, the
// `always` procedure in its four spellings -- `always` (§9.2.2.1),
// `always_comb` (§9.2.2.2), `always_latch` (§9.2.2.3) and `always_ff`
// (§9.2.2.4) -- and the `final` procedure of §9.2.3. None of the six changes
// what a statement inside it may contain, so a check over a procedural
// statement reaches all six.
//
// The answer lives beside ModuleItemKind rather than inside the validator that
// first needed it, because a caller that spells the set out for itself omits
// part of it. Every such caller listed `always` and `initial` and left the four
// remaining kinds unchecked, which meant a source rejected when its statement
// sat in `always` was accepted when the same statement sat in `always_comb`.
// Written here, a seventh procedural kind added to the enum is added to the
// predicate in the same place.
//
// §9.2 also names a task and a function structured procedures. Neither is one
// of these six: ModuleItemKind gives each its own kind, and a caller that walks
// `ModuleItem::body` finds nothing there for either, because a task or function
// declaration carries its statements under its own declaration rather than
// inline.
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

// The type A.3.4 gives a gate or switch keyword, which is what A.3.1's
// instance productions are written against: cmos_switchtype is `cmos | rcmos`,
// enable_gatetype `bufif0 | bufif1 | notif0 | notif1`, mos_switchtype `nmos |
// pmos | rnmos | rpmos`, n_input_gatetype `and | nand | or | nor | xor |
// xnor`, n_output_gatetype `buf | not`, pass_en_switchtype `tranif0 | tranif1
// | rtranif1 | rtranif0` and pass_switchtype `tran | rtran`. The pull gate is
// A.3.1's own, `pullup` and `pulldown` opening pull_gate_instance with no type
// production of their own, and stands here as the eighth so that every
// GateKind has a type.
enum class GateType : uint8_t {
  kCmosSwitch,
  kEnableGate,
  kMosSwitch,
  kNInputGate,
  kNOutputGate,
  kPassEnSwitch,
  kPassSwitch,
  kPullGate,
};

// The A.3.4 type of a gate kind. Written beside GateKind for the reason
// IsProceduralItemKind below is written beside ModuleItemKind: what A.3.1
// lets an instance carry -- a drive_strength, a delay2 or a delay3, and how
// many terminals -- is given per type, and a caller that spells a type's
// kinds out for itself is one more list to keep whole. A kind added to the
// enum is added to its type in the same place.
inline GateType GateTypeOf(GateKind kind) {
  switch (kind) {
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
      return GateType::kNInputGate;
    case GateKind::kBuf:
    case GateKind::kNot:
      return GateType::kNOutputGate;
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
      return GateType::kEnableGate;
    case GateKind::kTran:
    case GateKind::kRtran:
      return GateType::kPassSwitch;
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      return GateType::kPassEnSwitch;
    case GateKind::kNmos:
    case GateKind::kPmos:
    case GateKind::kRnmos:
    case GateKind::kRpmos:
      return GateType::kMosSwitch;
    case GateKind::kCmos:
    case GateKind::kRcmos:
      return GateType::kCmosSwitch;
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return GateType::kPullGate;
  }
  return GateType::kPullGate;
}

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

  // §27.6 gave this generate block its name -- "All unnamed generate blocks
  // will be given the name genblk<n>" -- rather than the source writing one.
  // §23.6 rules that objects declared in an unnamed generate block "can be
  // referenced by hierarchical names only from within the block and within any
  // hierarchy instantiated by the block", so a path written outside must not
  // reach through the name even though elaboration has one to spell. The name
  // is assigned into the field the source would have filled, so nothing
  // downstream can tell the two apart without this.
  bool name_is_generated = false;

  // True when the block held in body was written with the `begin` and `end`
  // keywords, false when it was written as a single item without them. A.4.2
  // gives `generate_block ::= generate_item | [ generate_block_identifier : ]
  // begin [ : generate_block_identifier ] { generate_item } end
  // [ : generate_block_identifier ]`, so the two forms are told apart only
  // while the block is being parsed. §27.5 needs the distinction afterwards:
  // "If a generate block in a conditional generate construct consists of only
  // one item that is itself a conditional generate construct and if that item
  // is not surrounded by begin-end keywords, then this generate block is not
  // treated as a separate scope."
  bool has_begin_end = false;

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

// §16.7's cycle_delay_range as the linear sequence monitor reads it: the
// number of clock ticks from the operand before to the one this stands
// before, `##N` being [N:N], `##[a:b]` the closed range, `##[a:$]` a range
// with no upper bound, `##[*]` [0:$] and `##[+]` [1:$].
// A bound written as the name of a formal argument of the declaring sequence
// is kept by name until §16.8's instantiation supplies the actual, an
// elaboration-time constant or `$`, that the flattening reads it as.
struct SeqCycleDelay {
  static constexpr uint32_t kUnbounded = UINT32_MAX;
  uint32_t min = 1;
  uint32_t max = 1;
  std::string_view min_formal;
  std::string_view max_formal;
};

// §16.10: one assignment of a sequence_match_item, `lvar = rhs` or
// `lvar op= rhs`, executed when the operand it stands with holds, or, where
// `init` is set, before that operand is evaluated: §16.8.2's initialization
// assignment of a local variable formal argument at the beginning of an
// attempt of the instance.
struct SeqMatchAssign {
  std::string_view lvar;
  TokenKind op = TokenKind::kEq;
  Expr* rhs = nullptr;
  bool init = false;
  // §16.11: a subroutine call attached to the sequence in place of an
  // assignment, executed at each end point in the Reactive region with its
  // by-value arguments as they read at the match; `lvar` and `rhs` are unset
  // where this is.
  Expr* call = nullptr;
  // §16.10 and §16.13.7: where `lvar` names a local of a named property, the
  // literal standing for the attempt's copy of it, which the property's other
  // expressions read in the local's place; the item assigns the copy by
  // rewriting the literal. Null for any other target.
  Expr* local_copy = nullptr;
};

// §16.10: a local variable of a sequence body, one an
// assertion_variable_declaration declares or, in the flattened form, a local
// variable formal argument of an instance, with the keyword of its type and
// its declaration assignment where it has one.
struct SeqLocalDecl {
  std::string_view name;
  TokenKind type_kw = TokenKind::kKwInt;
  Expr* init = nullptr;
};

// §16.9.2: the repetition written after an operand of a linear body: none,
// consecutive `[*min:max]` on a Boolean or a group, goto `[->min:max]` or
// nonconsecutive `[=min:max]` on a Boolean, the count an exact `[*n]` being
// [n:n], `[*]` [0:$] and `[+]` [1:$], `$` kept as SeqCycleDelay::kUnbounded.
struct SeqRepetition {
  enum class Kind : uint8_t { kNone, kConsecutive, kGoto, kNonconsecutive };
  Kind kind = Kind::kNone;
  uint32_t min = 1;
  uint32_t max = 1;
};

// §16.9.9: `exp throughout seq` inside a chain, `(exp)[*0:$] intersect seq`,
// which matches where seq does and exp holds at every tick of the match: the
// condition, the operands of the chain from `first` to `last` that seq
// became, and seq's own leading delay, `lead` ticks by which the first
// operand's delay exceeds the delay written before the throughout, so that
// the interval exp holds over begins where seq begins rather than where its
// first operand is read.
struct SeqThroughout {
  Expr* cond = nullptr;
  size_t first = 0;
  size_t last = 0;
  uint32_t lead = 0;
};

// §16.13.6/§9.4.4: the linear form of a sequence body, `[##d0] b0 ##d1 b1
// ... ##dn bn` (each bi a Boolean, each di one of §16.7's cycle_delay_range
// forms, each operand carrying the §16.10 match items written with it), which
// the parser captures for the simulator's sequence monitor. The delay before
// each operand is parallel to the operands, the first one the leading delay,
// 0 where none is written.
struct SeqLinearBody {
  std::vector<Expr*> operands;
  std::vector<SeqCycleDelay> delays;
  std::vector<std::vector<SeqMatchAssign>> match_items;
  // §16.9.2: the repetition each operand carries, parallel to the operands.
  std::vector<SeqRepetition> repetitions;
  std::vector<SeqLocalDecl> locals;
  // §16.9.9: the conditions held throughout spans of this chain.
  std::vector<SeqThroughout> throughouts;
  // §16.9.6: the other operands of an `intersect` this chain is the first
  // operand of, each a chain of its own that must match from the same tick
  // and end at the same tick as this one; §16.9.1 has `intersect` bind
  // tighter than `and` and looser than `##`.
  std::vector<SeqLinearBody> intersects;
  // §16.9.5: the other operands of an `and` this chain is the first operand
  // of, each a chain of its own, with its intersects, that must match from
  // the same tick, the whole ending at the later of the end points; §16.9.1
  // has `and` bind tighter than `or` and looser than `intersect`.
  std::vector<SeqLinearBody> conjuncts;
  // §16.9.7: the operands of a top-level `or`, each a chain, with its
  // conjuncts, of its own beside this one, the sequence matching where any of
  // them does; §16.9.1 has `or` bind loosest, so each runs from one `or` to
  // the next.
  std::vector<SeqLinearBody> alternatives;
  // §16.9.8: whether the whole body is the operand of `first_match`, so
  // that of an attempt's matches only those ending earliest count, and the
  // match items written after the operand inside its parentheses, executed
  // at the end of each of those matches.
  bool first_match = false;
  std::vector<SeqMatchAssign> first_match_items;
  // §16.13.1: the clocking event each operand of the chain is evaluated on
  // where the chain writes one before an operand, `##1 @(posedge clk1) b`,
  // the event in force from that operand on; parallel to the operands once
  // any is written, an operand before the first one written carrying none,
  // which is the leading clock's, and empty where the chain writes none.
  std::vector<std::vector<EventExpr>> clocks;
  // §16.13.3: the clock in force at the end of the chain, which flows out
  // of the sequence to what follows it, an implication's consequent among
  // others; a clock named inside parentheses or an instance flows no
  // further than them. Empty where the clock flowing in flows out.
  std::vector<EventExpr> clock_out;
};

struct ModuleItem {
  ModuleItemKind kind;
  SourceLoc loc;
  std::vector<Attribute> attrs;

  bool from_anonymous_program = false;

  // §13.3.1 (printed page 339) and §13.4.2: the lifetime keyword written after
  // `function` or `task`, `function static f()`, which makes every variable
  // of the subroutine one cell shared by all its activations; is_automatic is
  // the `automatic` keyword in the same position. Both false where the
  // declaration writes neither and the scope's default decides.
  bool is_automatic = false;
  bool is_static = false;
  // §8.10 (printed pages 186 and 187): the `static` method qualifier written
  // before `function` or `task` in a class, `static function f()`, which makes
  // the method callable with no object and gives it no `this`. §8.10 sets it
  // apart from the lifetime above: a static method's variables are automatic,
  // as every class method's are (§13.3.1, printed page 339), and a class
  // method carrying the static lifetime is illegal. The parser once folded
  // the qualifier into is_static, so §13.5.2's ban on a ref formal in a
  // static-lifetime subroutine refused a class static method's ref formal.
  bool is_static_method = false;

  bool is_extern = false;
  bool is_forkjoin = false;

  bool is_localparam = false;

  // A.2.1.3: one data_declaration carries a list_of_variable_decl_assignments,
  // and each declarator in that list becomes its own item. False on every
  // declarator after the first, so that what the declaration as a whole
  // introduces once -- an inline enumeration's named constants, say -- is not
  // taken to be introduced again by each name in the list.
  bool first_in_decl_list = true;

  // §27.4: set on the declaration produced by `genvar i;`. A genvar is parsed
  // as a variable declaration because that is its shape, but it "is used as an
  // integer during elaboration to evaluate the generate loop and create
  // instances of the generate block, but it does not exist at simulation
  // time", so the elaborator must be able to tell the two apart.
  bool is_genvar = false;

  // §6.18: set where the declaration was written as two bare identifiers and a
  // semicolon and the first named nothing the parser had yet seen declared as a
  // type. §6.18 rules that "The declaration of a user-defined data type shall
  // precede any reference to its type_identifier", and that shape is the one a
  // reference breaching it shares with a module instantiation written without
  // its port connection list. The parser cannot tell the two apart: it holds no
  // table of module names, and a module may be instantiated above its own
  // declaration. Elaborator::ReportUndeclaredTypeName decides and reports,
  // because the elaborator is what knows the module names.
  bool type_name_undeclared_at_parse = false;

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
  // Whether this instance is the second or a later hierarchical_instance of
  // one instantiation, `chk c1(a), c2(b);`. A.4.1.1's module_instantiation,
  // A.4.1.2's interface_instantiation and A.4.1.3's program_instantiation
  // write `hierarchical_instance { , hierarchical_instance }`; A.4.1.4's
  // checker_instantiation writes one name_of_instance, and the elaborator,
  // which knows what the cell is, reads this to hold a checker to it.
  bool inst_continues_list = false;
  Expr* inst_range_left = nullptr;
  Expr* inst_range_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> inst_dims;

  DataType typedef_type;
  std::string_view typedef_ifc_port;
  std::string_view nettype_resolve_func;
  // §6.6.7's Syntax 6-1 writes the with clause as
  // `with [ package_scope | class_scope ] tf_identifier`, so the resolution
  // function may be named through a package or a class. This holds that
  // qualifier -- the text before `::` -- and is empty when the clause carried
  // none. It is a separate field from nettype_resolve_func because the two are
  // separate names: a bare function name alone cannot say which scope was
  // written, so a declaration reading `with C::res` and one reading `with res`
  // recorded the same thing and bound to the same function.
  //
  // One field rather than a list, because the grammar admits one qualifier and
  // not a chain.
  std::string_view nettype_resolve_scope;

  Stmt* gen_init = nullptr;
  Expr* gen_cond = nullptr;
  Stmt* gen_step = nullptr;
  std::vector<ModuleItem*> gen_body;
  // True when the block held in this item's own gen_body was written with the
  // `begin` and `end` keywords, false when it was written as a single item
  // without them. A.4.2 gives `generate_block ::= generate_item |
  // [ generate_block_identifier : ] begin [ : generate_block_identifier ]
  // { generate_item } end [ : generate_block_identifier ]`, so the two forms
  // are told apart only while the block is being parsed. §27.5 needs the
  // distinction afterwards: "If a generate block in a conditional generate
  // construct consists of only one item that is itself a conditional generate
  // construct and if that item is not surrounded by begin-end keywords, then
  // this generate block is not treated as a separate scope." The else branch
  // of an if_generate_construct is its own ModuleItem, reached through
  // gen_else, and records its block on that item's field rather than on this
  // one.
  bool gen_body_has_begin_end = false;

  // §27.6 gave this generate block its name -- "All unnamed generate blocks
  // will be given the name genblk<n>" -- rather than the source writing one.
  // §23.6 rules that objects declared in an unnamed generate block "can be
  // referenced by hierarchical names only from within the block and within any
  // hierarchy instantiated by the block", so a path written outside must not
  // reach through the name even though elaboration has one to spell. The name
  // is assigned into the field the source would have filled, so nothing
  // downstream can tell the two apart without this.
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
  bool is_ansi_ports = false;
  std::vector<FunctionArg> func_args;
  std::vector<Stmt*> func_body_stmts;

  std::vector<std::pair<Expr*, Expr*>> defparam_assigns;

  std::vector<Expr*> alias_nets;

  Expr* assert_expr = nullptr;
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  // §16.12.1: for a concurrent assertion whose property_spec is an instance of
  // a named property written without arguments, the property's name. The
  // parser cannot tell such a name from a variable's, so it records the name
  // and the elaborator substitutes the property's body in place of the
  // instance, or reports why it cannot. Empty for every other property_spec.
  std::string_view prop_instance_name;
  // §16.12.1: for a named property whose body is the clocked boolean form
  // `@(event) boolean_expression`, the leading clocking event and the boolean,
  // captured by the parser so an instance of the property can be evaluated as
  // an assertion written in that form is. Both empty for any other body.
  std::vector<EventExpr> prop_clock;
  Expr* prop_body_expr = nullptr;
  // §16.12: the disable condition of that body's property_spec, where it
  // carries a `disable iff` between the clock and the boolean.
  Expr* prop_disable_iff = nullptr;
  // §16.12.3: whether that body's boolean stands under `not`.
  bool prop_negated = false;
  // §16.12: for a named property whose body is a property the tree
  // evaluator reads, that body as a tree, its clock and disable condition
  // in prop_clock and prop_disable_iff as the clocked boolean form's are;
  // null for the clocked boolean form and for any other body. §16.12.17:
  // an instance of the property in the tree, its own included, is expanded
  // when it begins.
  PropertyExprNode* prop_body_tree = nullptr;
  // §16.10 and §16.13.7: the local variables the body declares ahead of
  // the property, each with the keyword of its type and its initialization
  // assignment where it has one, a copy of each made for an evaluation
  // attempt of an instance and initialized at the first tick of the clock
  // the copy is for.
  std::vector<SeqLocalDecl> prop_locals;

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
  //   prop_untimed_instance_refs: every property instance reached in the body
  //     with no preceding positive time advance — the zero-weight out-edges of
  //     the dependency digraph. A cycle built solely from such edges has total
  //     weight zero, which Restriction 3 forbids (the mutual-recursion case as
  //     well as the direct self-loop).
  std::vector<std::string_view> prop_negated_instance_refs;
  std::vector<std::string_view> prop_untimed_instance_refs;
  std::vector<bool> prop_formal_is_local;
  // §16.12.18: parallel to prop_formals; true when the formal was declared with
  // type `property`. Such a formal may not be referenced as the antecedent of
  // an implication (§16.12.7), which the body scan enforces.
  std::vector<bool> prop_formal_is_property;
  std::vector<PropertyInstanceArgInfo> prop_instance_args;
  bool prop_has_untimed_self_recursion = false;

  // §16.8.2: per-formal direction when the formal is designated as a local
  // variable argument. Length matches the number of local-marked formals in
  // declaration order; non-local formals are not represented here.
  std::vector<Direction> prop_seq_local_lvar_directions;

  // §16.8: parallel to prop_formals; true when the formal has a default actual
  // argument declared (`formal = default_expression`). Used by the elaborator
  // to decide which formals an instance must supply an actual for.
  std::vector<bool> prop_formal_has_default;
  // §16.14.7: parallel to prop_formals; which of the two inferred functions
  // the formal's default value is, $inferred_clock or $inferred_disable, or
  // neither, the elaborator putting the clocking event or the disable
  // condition inferred at the instance in the formal's place.
  std::vector<InferredDefault> prop_formal_inferred;

  // §16.8.1: parallel to prop_formals; the keyword of the type a formal was
  // declared with, applying to every formal that follows the keyword and
  // precedes the next, kEof where the formal is untyped or its type is one no
  // keyword alone names, a packed vector or a user-defined type. The sequence
  // flattening casts an actual to a keyword type and reads an `event` formal
  // as the clock's event expression.
  std::vector<TokenKind> prop_formal_type_kw;

  // §16.10: identifiers introduced by assertion_variable_declaration items in
  // the body of a sequence or property declaration. Each entry is one local
  // variable declared in the body (a single declaration with N comma-
  // separated names produces N entries).
  std::vector<std::string_view> prop_seq_assert_vars;

  std::vector<EventExpr> clocking_event;

  // §16.13.6/§9.4.4: for a named sequence whose body the parser captured in
  // its linear form, the clocking event and that form. Captured so the
  // simulator can run a monitor that fires the sequence's endpoint event on a
  // match and make `sequence.triggered` work. A dedicated field (not
  // clocking_event, which marks a clocking block) so clocking-block validation
  // is unaffected. Both empty for any other sequence shape.
  std::vector<EventExpr> seq_clock;
  SeqLinearBody seq_linear;

  // §16.16(b1): true when this property or sequence declaration's body begins
  // with an explicit leading clocking event (a `@(...)`). Recorded so a
  // declaration placed inside a clocking block, where such an explicit event is
  // disallowed, can be rejected at parse time. Meaningful only for
  // kPropertyDecl/kSequenceDecl items.
  bool decl_has_leading_clock = false;

  // §16.16(b2): number of explicit clocking events (`@(...)`) appearing in this
  // property or sequence declaration's body. Together with decl_has_leading_
  // clock it distinguishes a singly clocked declaration (one leading event)
  // from a multiclocked one (a non-leading event, or more than one), so a
  // multiclocked declaration inside a clocking block can be rejected.
  int decl_clock_event_count = 0;

  std::vector<ClockingSignalDecl> clocking_signals;
  // §16.16 (b): the property and sequence declarations of a clocking block,
  // each clocked by the block's event and named through the block,
  // `posedge_clk.q4`, where an assertion instantiates it.
  std::vector<ModuleItem*> clocking_decls;
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
  // §25.5.4: set for the `.port_id(expr)` modport-expression form (including
  // the empty `.port_id()` form). Distinguishes a named port — whose identifier
  // is a fresh port name that need not be a declared interface item — from a
  // bare simple port identifier, which must reference a declared interface
  // item.
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

  // Annex E: the default decay time, charge strength and delay mode in force
  // where this module was declared, put here by ApplyModuleDirectives from
  // what the preprocessor recorded; `has_module_directives` is false for a
  // module parsed without the preprocessor, which then takes the compilation
  // unit's values.
  bool has_module_directives = false;
  uint64_t default_decay_time = 0;
  bool default_decay_time_infinite = true;
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
  // §13.3.1: a package declared `automatic` makes its subroutines default to
  // automatic lifetime; otherwise their default lifetime is static. Kept last
  // so adding it does not shift the offsets of the fields above.
  bool is_automatic = false;
};

}  // namespace delta
