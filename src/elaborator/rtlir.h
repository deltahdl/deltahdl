#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;
  std::string_view string_value;
};

enum class RtlirNodeKind : uint8_t {
  kModule,
  kPort,
  kNet,
  kVariable,
  kContAssign,
  kProcess,
  kParamDecl,
  kModuleInst,
};

enum class RtlirProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
  kFinal,
};

// §7.4.2: one element address range of an unpacked dimension, as the
// declaration wrote it -- the first bound and the second, in that order.
//
// The order is the record. §7.4.2 rules that "the first value may be greater
// than, equal to, or less than the second value", so `[1:4]` and `[4:1]` are
// different declarations, and a single low bound cannot tell them apart.
// §11.5.2 is what reads them: "the address bounds given in the declaration of
// the memory determine the effect of the address expression. If the address is
// invalid (it is out of bounds or has one or more x or z bits), then the value
// of the reference shall be as described in 7.4.5". A dimension written
// `[size]` is recorded here as `[0:size-1]`, which §7.4.2 makes it mean.
//
// The bounds are int64_t because §7.4.2 admits "any integer value -- positive,
// negative, or zero", and an unsigned field turns `[-3:5]` into a bound no
// address reaches.
struct RtlirUnpackedDim {
  int64_t left = 0;
  int64_t right = 0;

  // The address a dimension counts from, which is the smaller bound whichever
  // way it was written.
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
  uint32_t width = 1;
  bool is_signed = false;

  // The type the port header declared, carried so a select on the port can be
  // resolved against the packed dimension as written. §11.5.1: "the actual bit
  // that is accessed by an address is, in part, determined by the
  // declaration", and `width` above says how many bits the port has rather
  // than which bit an index names -- `[15:0]` and `[2:17]` are both sixteen
  // bits wide, and index 2 reaches a different bit of each. Set when the port
  // declares a packed dimension. Also set, to the resolved aggregate, for a
  // port §23.2.2.3 makes a net whose data type is a packed structure or union
  // (§6.7.1), which declares no variable to carry a layout of its own; the
  // simulator lays the net's members out from it (§7.2.1). Null otherwise,
  // which leaves the port addressed as [0:0].
  const DataType* dtype = nullptr;

  bool is_var = false;
  // §23.2.2.3: the net type of a port the clause makes a net -- the net type
  // keyword the declaration wrote, or the default net type where it wrote
  // none, since "an implicit data type declaration implies a net unless the
  // var keyword is used" and an input or inout with no port kind "shall default
  // to a net of default net type". kNone for a port the clause makes a
  // variable, which is the same set is_var names; carried separately because
  // which net type it is is a second question is_var does not answer.
  NetType net_type = NetType::kNone;
  bool is_interconnect = false;
  bool is_interface_port = false;
  std::string_view interface_type_name;
  // §23.2.2.4: the default value of an input port, which an instantiation that
  // leaves the port unconnected takes as its connection. Null for every other
  // port.
  Expr* default_value = nullptr;
  // §23.2.2.2, Syntax 23-4's `[ = constant_expression ]` on a variable output
  // port, which its footnote 2 permits as the one initialization a port takes:
  // the value the port's variable holds before any procedure runs, as a
  // variable declaration's initializer is. Null for every other port.
  Expr* init_value = nullptr;
  std::vector<ResolvedAttribute> attrs;
  // The number of unpacked dimensions the port declaration wrote, whether or
  // not each one folded to constants. A count larger than unpacked_dims.size()
  // says a dimension went unrecorded, which is what tells a consumer that the
  // port is an array it cannot address from a port that is not an array at all.
  uint32_t num_unpacked_dims = 0;
  std::vector<uint32_t> unpacked_dim_sizes;
  // §11.5.2: the address bounds of each dimension that folded, in declaration
  // order. unpacked_dim_sizes beside it says how many elements a dimension
  // holds and this says which addresses reach them, which are different
  // questions for every dimension not written `[0:n]`.
  std::vector<RtlirUnpackedDim> unpacked_dims;

  // §37.3.3: where the port declaration stands, which vpiLineNo and vpiFile are
  // read off for the port object §37.14's instance-to-port relation reaches.
  SourceLoc loc;
};

struct RtlirNet {
  std::string_view name;
  NetType net_type = NetType::kWire;
  uint32_t width = 1;

  // §11.5.1: "the actual bit that is accessed by an address is, in part,
  // determined by the declaration" -- a width alone does not say which bit an
  // index names, because `[15:0]` and `[2:17]` are both sixteen bits wide and
  // the same index addresses a different bit of each. Set when the declaration
  // carries a packed dimension, so a select on this net can be resolved against
  // the range as written. Also set, to the resolved aggregate, for a net of a
  // packed structure or union with no dimension of its own (§6.7.1), so a
  // member select of the net names the run of bits §7.2.1 lays the member out
  // at. Null for a scalar, which is addressed as [0:0].
  const DataType* dtype = nullptr;

  // §7.4.2 with §20.6.2: the unpacked dimensions the declaration wrote after
  // the name, `wire [7:0] w[3]` having one of size 3. `width` is the bits of
  // one element, so the bits the net holds in all -- what $bits(w) answers,
  // 24 -- are width times every size here, and a net with none of them is a
  // vector of width bits. num_unpacked_dims counts every dimension written;
  // unpacked_dim_sizes holds the size of each dimension whose bounds folded,
  // in declaration order, so a vector shorter than num_unpacked_dims does not
  // line up with the declaration and sizes nothing.
  uint32_t num_unpacked_dims = 0;
  std::vector<uint32_t> unpacked_dim_sizes;

  bool is_signed = false;
  std::vector<uint32_t> driver_indices;

  Strength charge_strength = Strength::kMedium;
  uint32_t trireg_capacitance = 0;

  // §28.16.2.2: the charge decay time of a trireg net, counted in time units,
  // which the declaration writes as its third delay: "The third delay in a
  // trireg net declaration shall specify the charge decay time." Only a trireg
  // carries one, because §28.16.2 gives the third delay of every other net to
  // "the delay in a transition to the z logic state" instead.
  uint64_t decay_ticks = 0;

  // Whether this net decays at all, which a count of zero cannot say.
  // §28.16.2.1 makes the decay a process that ends when "the delay specified by
  // charge decay time elapses, and the trireg net makes a transition from 1 or
  // 0 to x", so a decay time of zero is that transition happening at once and
  // not one that never happens; §28.16.2.2 gives the third delay's *absence*
  // the meaning of never decaying. The two used to share a representation, and
  // a declaration writing zero got the opposite of what it asked for.
  //
  // This is the shape CompilationUnit::default_decay_time_infinite already uses
  // for the `default_decay_time directive, which records an infinite decay
  // separately from a count for the same reason.
  bool decays = false;

  // §28.16: the net delay this net was declared with. "Net delays refer to the
  // time it takes from any driver on the net changing value to the time when
  // the net value is updated and propagated further", so the delay belongs to
  // the net and every driver of it waits the delay out, whatever construct the
  // driver is written as. §10.3.3 excludes the declaration that also assigns
  // the net -- "When there is a continuous assignment in a declaration, the
  // delay is part of the continuous assignment and is not a net delay. Thus, it
  // shall not be added to the delay of other drivers on the net" -- so these
  // are null for such a declaration, whose delay stays on the continuous
  // assignment RtlirModule::assigns holds for it. They are null as well for a
  // declaration that wrote no delay at all.
  //
  // The three are §28.16's rise, fall and turn-off delays, chosen between by
  // Table 28-9. §28.16.1 lets any one of them be written as a min:typ:max
  // triple, which is a property of the expression in the slot and not of the
  // slot, so it does not change what the three are. delay_turnoff is null on a
  // trireg net, whose third delay §28.16.2 makes "the charge decay time instead
  // of the delay in a transition to the z logic state" -- decay_ticks above
  // carries that one.
  Expr* delay_rise = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_turnoff = nullptr;

  bool is_vectored = false;
  bool is_scalared = false;

  bool is_user_nettype = false;
  std::string_view resolve_func;

  std::string_view nettype_name;
  std::vector<ResolvedAttribute> attrs;

  // §37.3.3: where the declaration that made this net stands. The two location
  // properties that clause gives every object corresponding to source text --
  // vpiLineNo and vpiFile -- are read off this, so a net whose declaration was
  // not recorded here answers neither. Invalid for a net no declaration
  // produced, an implicitly declared one among them.
  SourceLoc loc;

  // §23.4: whether this net stands for an object of a lexically enclosing
  // module rather than one of this module's own. The outer name space is
  // visible to a module declared and instantiated inside another, so a name a
  // continuous assignment or port connection in the nested module writes may
  // be one an enclosing module declares; the elaborator still pushes a net of
  // that name onto the nested module's list, for its assignment to be lowered
  // against, and marks it here so that no instance materializes it -- a net of
  // the name under the instance would shadow the outer object and take the
  // assignment with it. False for a net the module declares, which §23.4 has
  // hide an outer name, and for an implicit net of a name declared nowhere,
  // which §6.10 gives to the scope the reference appears in, so each instance
  // of the nested module has its own.
  bool refers_outward = false;
};

struct RtlirVariable {
  std::string_view name;
  uint32_t width = 1;
  bool is_4state = true;
  bool is_event = false;
  bool is_string = false;
  bool is_real = false;
  bool is_signed = false;
  bool is_chandle = false;
  const Expr* init_expr = nullptr;
  const DataType* dtype = nullptr;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  // §36.12.1 Table 36-10 rows 3 and 4: what the declaration named this
  // variable, which is the box §37.17 draws it in - an integer var, a time var,
  // a real var and so on. The flags above answer a few of those questions and
  // no others, and `dtype` is carried only where the declaration wrote a packed
  // dimension, so neither says what a plain `integer i;` is. kImplicit for a
  // declaration that named no type of its own.
  DataTypeKind decl_kind = DataTypeKind::kImplicit;
  uint32_t unpacked_size = 0;
  // The address the first unpacked dimension counts from. int64_t because
  // §7.4.2 admits a negative bound, and `int x [-3:5]` counts from -3.
  int64_t unpacked_lo = 0;
  bool is_descending = false;
  // §7.4.2: full per-dimension extents of a fixed multidimensional unpacked
  // array, outermost first, so the simulator can materialize one leaf variable
  // per element (arr[i0][i1]...) and distribute a nested assignment pattern
  // into it. Populated only when every unpacked dimension is a fixed
  // range/const dimension; left empty for single-dimension, queue, dynamic, or
  // associative arrays (which keep the single-dimension
  // unpacked_size/unpacked_lo above).
  std::vector<uint32_t> unpacked_dim_sizes;
  // §11.5.2: the address bounds of each unpacked dimension that folded to
  // constants, in declaration order, filled for a one-dimensional declaration
  // as well as a multidimensional one. unpacked_size, unpacked_lo and
  // is_descending above summarize the first of these and describe no other.
  std::vector<RtlirUnpackedDim> unpacked_dims;
  // The number of unpacked dimensions the declaration wrote, counting one whose
  // bounds did not fold and one written `[]`. Without it `logic [7:0] m [1:4]`
  // and `logic [7:0] m [1:4][]` record the same thing, and a consumer reads the
  // second as an array of words it can address.
  uint32_t num_unpacked_dims = 0;
  bool is_dynamic = false;
  bool is_queue = false;
  int32_t queue_max_size = -1;
  // §7.4 with §7.10: whether each element of the queue, dynamic array or
  // associative array the first dimension declares is itself a queue -- a
  // second dimension `[$]`, `int aq[string][$]`, or a type naming a queue
  // typedef, `q_t d[]` under `typedef int q_t[$];`.
  bool elements_are_queues = false;
  bool is_assoc = false;
  bool is_string_index = false;
  bool is_wildcard_index = false;
  bool is_class_index = false;
  // Signedness of an integral associative-array index type. Determines whether
  // an index expression is sign- or zero-extended to the index width and the
  // resulting key ordering (§7.8.4). Built-in integral index types are signed.
  bool is_index_signed = true;
  uint32_t assoc_index_width = 32;
  std::string_view assoc_index_class_name;
  std::string_view class_type_name;
  // §8.25: the declaration's own data type where it names a class, which is
  // where a specialization's parameter value assignment stands, `G #(5) b`
  // and `pool #(string, int) p`: the actuals the lowerer binds on the object
  // the variable's `new` constructs. Null for a variable of any other type.
  const DataType* class_data_type = nullptr;
  std::string_view enum_type_name;
  std::vector<ResolvedAttribute> attrs;

  // §37.3.3: where the declaration that made this variable stands, which
  // vpiLineNo and vpiFile are read off exactly as they are for a net. Invalid
  // for a variable the elaborator synthesized rather than read out of a
  // declaration, which corresponds to nothing in the source text to report.
  SourceLoc loc;
};

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  uint32_t width = 0;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;

  bool from_nonresistive_switch = false;

  bool from_resistive_switch = false;

  Expr* data_input = nullptr;

  // §28.6: the two terminals of a three-state gate, kept because Table 28-5
  // answers by them rather than by the value the gate's own expression yields.
  // With a control of x or z the gate drives L or H -- "a result that has a
  // value 0 or z" and "a value 1 or z" -- which is one side of the strength
  // scale rather than a value, so the strength a drive carries depends on the
  // control and on the value the gate would transmit. `three_state_pass` is
  // that value, the data terminal as the gate passes it, so a notif's inversion
  // is already in it. Null for every assignment that is not one of §28.6's four
  // gates.
  Expr* three_state_ctrl = nullptr;
  Expr* three_state_pass = nullptr;
  // §32.4.4: when this assignment is the §23.3.2 input port connection of a
  // module instance, the SDF names of the port it drives and of the signal it
  // drives it from -- the load and the source an interconnect entry annotates
  // between. Written the way an SDF file writes a hierarchical name, with `/`
  // between levels, because that is the spelling the annotator matched the
  // entry against. Both empty for every other continuous assignment, and the
  // source alone is empty where the connection is not a plain signal name, in
  // which case a PORT or NETDELAY delay -- which is the delay from all sources
  // -- still reaches the load.
  std::string interconnect_load;
  std::string interconnect_source;
  std::vector<ResolvedAttribute> attrs;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

// §29.8: one instance of a user-defined primitive, and what drives its output
// terminal. A gate instance lowers to an RtlirContAssign carrying a synthesized
// expression, and a primitive instance cannot, for two reasons. §29.3.4 defines
// the output as a table lookup rather than an operator, and §29.5 gives a
// sequential primitive a current state which "is considered equivalent to the
// current output value" and which an expression has nowhere to keep. So the
// instance carries the declaration it names, and the simulator evaluates that
// declaration's table against the input terminals, holding one UdpEvalState per
// instance for the length of the run.
//
// The terminals are split the way §29.8 writes them -- "udp_instance ::= [
// name_of_instance ] ( output_terminal , input_terminal { , input_terminal } )"
// -- so `inputs` already stands in the order UdpEvalState indexes a table row
// by, and nothing downstream has to work out which terminal is the output.
//
// Two delays and no third, because §29.8 rules that "Only two delays may be
// specified because z is not supported for UDPs". RtlirContAssign carries a
// third for the switches that need one.
struct RtlirUdpInst {
  const UdpDecl* decl = nullptr;
  // §29.8: "The instance name is optional, just as for gates." Empty where the
  // source wrote none, which is why it cannot be what identifies the instance.
  std::string_view name;
  // Where the primitive's name stands, which is the position a report about
  // this instance carries.
  SourceLoc loc;
  Expr* output = nullptr;
  std::vector<Expr*> inputs;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

struct RtlirAlias {
  std::vector<Expr*> nets;
};

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  // §16.5: true where this process carries a concurrent assertion's property
  // rather than a procedure the source wrote. §16.14.5 gives such an assertion
  // `always` semantics and the elaborator models it as kAlwaysFF, so the kind
  // alone cannot tell it from an always_ff procedure; §16.5 evaluates the
  // assertion in the Observed region and §16.5.1 samples the variables its
  // property reads, neither of which holds for the procedure.
  bool is_concurrent_clocked = false;
  // Where the keyword that opened this procedure stands. A report that rejects
  // the procedure itself rather than a statement within it has no other
  // position to name: body is a separate statement carrying its own.
  SourceLoc loc;
  // §16.9.4: the global clocking event an attempt of this process's property
  // has to reach before it can be evaluated, empty for every process whose
  // property names none of the five future sampled value functions. Those five
  // read a value "sampled at the next global clock tick", which no evaluation
  // standing at the assertion's own tick can read, and the clause says what to
  // do about it: "Execution of the action block of an assertion containing
  // global clocking future sampled value functions shall be delayed until the
  // global clocking tick that follows the last tick of the assertion clock for
  // the attempt." So the attempt waits for this event and is evaluated there,
  // where the values it names have been sampled.
  //
  // It is the effective global clocking declaration's event, copied per process
  // for the reason the sensitivity substitution above is made per process:
  // §14.14 rule b) can give two instances of one module different events.
  std::vector<EventExpr> gclk_future_event;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
  // §21.2.1.5 and §27.3: the generate block instances between the module
  // and the process, outermost first, each a level of the hierarchical name
  // %m reports from the process; empty for a process of the module itself.
  HierPath gen_block_path;
};

// §27.4 with §13.4 and §23.6: one subroutine declared in a generate block
// instance. The block "comprises a separate scope and a new level of
// hierarchy", so the subroutine is a member of the block instance's scope,
// which §23.6 names through the block, `blk[1].triple` for the instance of
// loop generate block blk at index 1, and its body reads the block's own
// declarations and the implicit localparam of each loop it is inside by their
// simple names. Every iteration of a loop generate block elaborates the one
// declaration, so RtlirModule::function_decls holds it once per instance and
// says nothing about which; this entry is what does. `gen_block_path` is the
// path §23.6 names the instance by, and the other two members are what an
// RtlirProcess of the same block carries, for the same reason: the body the
// instances share names the block's declarations plainly, and the process
// that calls the subroutine from outside the block stands in no such scope.
struct RtlirGenBlockSubroutine {
  ModuleItem* decl = nullptr;
  HierPath gen_block_path;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

struct RtlirParamDecl {
  std::string_view name;
  // §23.9: the generate block prefix in force where this parameter was
  // declared, empty for a parameter of the module itself. §23.9 lists "Generate
  // blocks" among the elements that "define a new scope", so a parameter
  // declared in one is not visible to a reference at module level or in a
  // sibling block, and a reader deciding what a bare identifier names has to be
  // able to tell the two apart.
  //
  // The scope is recorded here rather than folded into `name` the way
  // Elaborator::ScopedName folds it into RtlirNet::name and RtlirVar::name,
  // because every reader of RtlirModule::params matches a parameter by the
  // identifier the source wrote: Elaborator::BuildParamScope and
  // RegisteredModuleScope key a ScopeMap by it, ConstEvalString and
  // Elaborator::ResolveDefparamSteps compare it to a name out of the AST, and
  // ReportParamsMissingValue prints it into a §6.20.1 diagnostic. A prefixed
  // name would answer none of them.
  std::string_view gen_block_prefix;
  Expr* default_value = nullptr;
  // §23.10.2 with §6.20.2: the expression an instance's parameter value
  // assignment, or a configuration's (§33.4.3), gave this parameter, written
  // in the instantiating module, and null while the value is the declaration's
  // own or a defparam's (§23.10.1) that is not a literal. resolved_value is
  // 64 bits, and a parameter declared wider keeps its declared range through
  // every override, so the simulator evaluates the expression again at that
  // width (ReevaluateParamValue in src/simulator/lowerer_register.cpp): this
  // one in the instantiating instance, default_value in the declaring one. A
  // defparam's right-hand side stands in the scope of the defparam statement,
  // which the simulator cannot stand in, so of those only a literal, which
  // names nothing, is carried.
  const Expr* override_expr = nullptr;
  int64_t resolved_value = 0;
  // §6.20.2 with §23.10.1 and §23.10.2: the bits from 64 up of the value, as
  // ConstVal::high_words lays them out -- word i holding bits 64*(i+2)-1 down
  // to 64*(i+1) -- for a parameter declared wider than 64 bits whose value
  // was folded from an expression the fold cannot reach again where the name
  // is read: an instance override written in the instantiating module, a
  // defparam's right-hand side written in the module holding the statement,
  // and a parameter a defparam made over. Empty where no bit from 64 up is
  // set and where the value came from the declaration's own default or a
  // literal override, which RegisteredParamValue in
  // src/elaborator/const_eval_bits.cpp refolds. RecordResolvedHighWords there
  // fills it.
  std::vector<uint64_t> resolved_high_words;
  // §6.20.2 (printed pages 126-127): a parameter declared with neither a type
  // nor a range, or with a bare `signed`, takes the type and range of the
  // final value assigned to it, after every override -- a logic vector as
  // wide as that value. These are that value's self-determined width and
  // signedness where the value came from an expression the fold cannot reach
  // again where the name is read: an instance override written in the
  // instantiating module (§23.10.2), a defparam's right-hand side (§23.10.1),
  // and a parameter a defparam made over. A width of 0 says none was
  // recorded, and RegisteredParamValue in src/elaborator/const_eval_bits.cpp
  // then refolds the declaration's default or a literal override for it.
  // RecordResolvedHighWords there fills both as it fills
  // resolved_high_words.
  uint32_t value_width = 0;
  bool value_is_signed = false;
  // §6.20.2: a parameter declared with a real type takes a real value, which
  // resolved_value cannot hold. When is_real_value is set, resolved_real is the
  // parameter's value and resolved_value is not meaningful.
  double resolved_real = 0.0;
  bool is_real_value = false;
  // §6.16: a parameter declared with a string type takes a value of arbitrary
  // length. §6.16 rules that "strings can be of arbitrary length and no
  // truncation occurs", and resolved_value is 64 bits, so a value of more than
  // eight characters cannot be read back from it. resolved_string holds the
  // characters when is_string_value is set. resolved_value is still written for
  // such a parameter, because §11.10 packs a string literal into a constant
  // number and that is the form the rest of the elaborator reads.
  std::string_view resolved_string;
  bool is_string_value = false;
  bool is_resolved = false;
  bool is_localparam = false;
  bool from_override = false;
  bool is_unbounded = false;
  bool is_type_param = false;
  // Set when a configuration's parameter override fixed this value (§33.4.3).
  // Such a value takes precedence over a defparam targeting the same parameter,
  // so defparam application skips a parameter already locked by a config.
  bool config_locked = false;

  uint32_t decl_width = 0;
  bool decl_is_signed = false;
  bool has_decl_type = false;
  bool has_decl_range = false;
  // §11.5.1: the two bounds of the declared packed range, as written and
  // folded. The width alone does not say which bit an index reaches: the
  // clause sets `logic [15:0] acc` beside `logic [2:17] acc` and observes that
  // one value of an index addresses a different bit in each. Meaningful only
  // when has_decl_range_bounds is set, which requires both bounds to be
  // present and to fold where the declaration was elaborated.
  int64_t decl_range_left = 0;
  int64_t decl_range_right = 0;
  bool has_decl_range_bounds = false;
  // True when the declared data type is implicit (e.g. a bare `signed` or no
  // type keyword at all). Such a parameter, when it carries no range, takes its
  // range from the final value assigned to it rather than from a fixed declared
  // width (§6.20.2).
  bool decl_type_implicit = false;
  // §6.20.2 (printed page 126) with §23.10.1 (printed 764-765): the data type
  // the declaration was written with, whose packed range may name a parameter
  // a defparam later makes over -- `parameter logic [TOP:0] P` under `defparam
  // u.TOP = 7` -- so that Elaborator::RecomputeDependentParams can size the
  // parameter again from it with TOP's new value in scope, as decl_width and
  // the two bounds above were sized where it was declared. Null for a type
  // parameter and for a parameter port declared with no type. The AST owns
  // it.
  const DataType* decl_type = nullptr;
  // §23.10.1 (printed pages 764-765) with §6.20.2 (printed 126): the
  // right-hand side of the defparam that gave this parameter its value, the
  // values in scope where that statement stands, the generate blocks it
  // stands in (§23.9, printed 761, outermost first) and the module holding
  // it, kept so that Elaborator::RecomputeDependentParams, sizing the
  // parameter again once a later defparam changes its declared range, can
  // fold the expression over again and convert it to the new range, its
  // words above bit 63 recorded as Elaborator::ApplyDefparamSite records
  // them; the value converted to the earlier range had lost every bit
  // outside it, and a refold outside the blocks read a block's parameter as
  // its low 64 bits. Null and empty while no defparam has set the value.
  const Expr* defparam_value_expr = nullptr;
  std::unordered_map<std::string_view, int64_t> defparam_value_scope;
  GenBlockPrefixes defparam_value_scopes;
  const struct RtlirModule* defparam_module = nullptr;
  // §23.10.2 (printed page 766): the same for override_expr -- the values in
  // scope where the instantiation stands and the instantiating module, as
  // InstanceParamAssignments took them -- for a refold at a range a defparam
  // later gives the parameter. Null while no instance assigned the value.
  std::unordered_map<std::string_view, int64_t> override_scope;
  const struct RtlirModule* override_module = nullptr;
};

struct RtlirPortBinding {
  std::string_view port_name;
  Direction direction;
  Expr* connection = nullptr;
  uint32_t width = 1;
};

struct RtlirModuleInst {
  std::string_view module_name;
  std::string_view inst_name;
  // §23.6: the instance's name as the source wrote it, and the generate block
  // instances between it and the module holding it. RtlirModuleInst::inst_name
  // concatenates the two into one identifier, because the simulator keys an
  // instance's storage on a single flat string (Lowerer::LowerChildModules in
  // src/simulator/lowerer_child.cpp), and the steps cannot be recovered from it
  // -- a block named `g` holding `u` and a module-level instance named `g_u`
  // produce the same string. A hierarchical path is read against these two.
  std::string_view simple_inst_name;
  HierPath gen_block_path;
  struct RtlirModule* resolved = nullptr;
  std::vector<RtlirPortBinding> port_bindings;
  std::vector<ResolvedAttribute> attrs;
  bool is_bound = false;
  // §23.4: this instance's module, program or interface was declared inside
  // the module instantiating it, so "the outer name space is visible to the
  // inner module". A module declared elsewhere and merely instantiated here
  // gets no such visibility, which is the §23.9 module boundary.
  bool is_nested_decl = false;
};

struct RtlirImport {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
  // §26.3: an import makes the package's names candidates within the scope
  // that writes it and for references after it in that scope, and §27.5 makes
  // a generate block a scope of its own. An import a module writes directly
  // carries an empty prefix and binds its names under the instance alone. One
  // written inside a generate block carries a prefix of its own, which
  // Elaborator::ElaborateGenerateBlockImport also puts into the
  // GenBlockPrefixes of every process, continuous assignment and primitive
  // instance the block elaborates after the import, one step outside the
  // block's own prefix: SimContext::FindInGenerateBlock then answers a bare
  // name from the block's declarations first, then from this import, and only
  // then from the enclosing scope, while a process the block elaborated before
  // the import never carries it. The prefix is the block's prefix followed by
  // `:importN:`, which no declaration's key can spell.
  std::string_view scope_prefix;
};

struct RtlirEnumMember {
  std::string_view name;
  int64_t value = 0;
};

struct RtlirModule {
  std::string_view name;

  std::string_view library;
  bool has_param_port_list = false;
  bool is_program = false;
  bool is_interface = false;
  std::vector<ResolvedAttribute> attrs;
  // Annex E.4 to E.7: the delay mode the last directive before this module
  // selected, in force where the module was declared or, for a module parsed
  // without the preprocessor, the compilation unit's.
  DelayModeDirective delay_mode = DelayModeDirective::kNone;

  // Annex E.2 and E.3: the default decay time and charge strength for this
  // module's trireg nets that declare none, the directives in force where the
  // module was declared or, for a module parsed without the preprocessor, the
  // compilation unit's.
  uint64_t default_decay_time = 0;
  bool default_decay_time_infinite = true;
  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  // §20.4.1: the time unit and precision reported for this design element by
  // $timeunit/$timeprecision. Resolved from the element's own timeunit/
  // timeprecision declarations, falling back to the compilation unit's.
  TimeScale timescale;

  std::vector<RtlirPort> ports;
  std::vector<RtlirNet> nets;
  std::vector<RtlirVariable> variables;
  std::vector<RtlirContAssign> assigns;
  std::vector<RtlirUdpInst> udp_insts;
  std::vector<RtlirAlias> aliases;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  // §14.3's clocking blocks declared in this module, in source order. The item
  // is carried rather than resolved because §14.3 puts the clock, the skews and
  // the direction of each signal in it and the simulator's ClockingManager
  // wants all three; elaboration validates them (Elaborator::
  // ValidateClockingBlock) and this is what lets the run have them at all.
  std::vector<ModuleItem*> clocking_blocks;
  // §16.15: the condition of the module's default disable iff declaration,
  // which §16.14.7's $inferred_disable returns within its scope; nullptr
  // where the module declares none.
  Expr* default_disable_iff = nullptr;
  std::vector<ModuleItem*> function_decls;
  // §27.4 with §13.4: the subroutines declared in the module's named generate
  // block instances, each with the instance it belongs to, which
  // function_decls does not record; see RtlirGenBlockSubroutine.
  std::vector<RtlirGenBlockSubroutine> gen_block_subroutines;
  std::vector<ModuleItem*> let_decls;
  // §35.5.4's imported subroutines, declared in this module. They are held
  // apart from let_decls because §11.12's let is a substitution of the
  // expression its declaration writes, while an imported subroutine is a call
  // into a foreign function and carries no expression to substitute. Whatever
  // registers a run's imports reads this; RegisterModuleSubroutines in
  // src/simulator/lowerer_register.cpp registers let_decls and would otherwise
  // answer an import's name with a let expansion of nothing.
  std::vector<ModuleItem*> dpi_import_decls;
  // §35.7's exported subroutines, declared in this module. §35.7 states that
  // "Declaring a SystemVerilog function to be exported does not change its
  // semantics or behavior from the SystemVerilog perspective; there is no
  // effect on SystemVerilog usage other than making it possible for foreign
  // language tasks and functions in a DPI call-chain to call the exported
  // function", and an export declaration held in let_decls breaches that: it
  // carries no expression to substitute, so RegisterModuleSubroutines in
  // src/simulator/lowerer_register.cpp would answer the exported subroutine's
  // own name with a let expansion of nothing, ahead of the function itself.
  std::vector<ModuleItem*> dpi_export_decls;
  // §30.3's specify blocks, declared in this module: §30.3 states that a
  // specify block "shall appear inside a module declaration". What one declares
  // -- the module paths of §30.4, the PATHPULSE$ pulse limits of §30.7.1 and
  // the §30.7.4 pulse styles -- is timing data about the module rather than a
  // name a reference resolves to. They are held apart from let_decls for that
  // reason: RegisterModuleSubroutines in src/simulator/lowerer_register.cpp
  // registers each let_decls entry under item->name, which a specify block
  // leaves empty, and RangeHasName in
  // src/elaborator/elaborator_scope_rules_hier.cpp searches let_decls by name.
  std::vector<ModuleItem*> specify_blocks;
  // §28.4's gate instantiations, declared in this module, kept after
  // ElaborateGateInst (src/elaborator/elaborator_gates.cpp) has rewritten each
  // one into an RtlirContAssign on `assigns`. §32.4.1 has an SDF DEVICE entry
  // annotate the delay of the primitive instance itself, and
  // BuildPrimitiveDriversFromGate (src/simulator/specify_path_delay.h) reads
  // that delay off ModuleItem::gate_delay, gate_delay_fall and
  // gate_delay_decay. The continuous assignment the rewrite produces cannot
  // answer for it: ApplyGateDelays copies the three expressions onto
  // RtlirContAssign but drops which gate primitive and which output terminal
  // they belonged to, and one gate instantiation with several outputs becomes
  // several assignments. RegisterModuleGates (src/simulator/specify.h) walks
  // this list once per module instance to register those drivers.
  std::vector<ModuleItem*> gate_insts;
  // §6.20.5's specparams declared in the module body, outside every specify
  // block: "A specparam ... may be declared inside a specify block or in the
  // module body." Each entry is the name the specparam was lowered under, which
  // is Elaborator::ScopedName of the declared name, so a specparam declared in
  // a generate block carries that block's prefix. §32.4.3 has an SDF LABEL
  // section annotate to specparams and states no exception for either
  // declaration site, so RegisterModuleSpecparams (src/simulator/specify.h)
  // binds these to SpecifyManager beside the in-block ones
  // RegisterSpecifyBlocks binds. Names rather than ModuleItem pointers, because
  // the name a LABEL has to reach is the scoped one and the ModuleItem carries
  // only the bare name.
  std::vector<std::string_view> specparam_names;
  std::vector<ModuleItem*> sequence_decls;
  // §16.12: the module's named property declarations, which the run
  // registers so that an instance of one in a property tree is expanded,
  // §16.12.17's recursion included, when it begins.
  std::vector<ModuleItem*> property_decls;
  std::vector<ClassDecl*> class_decls;
  std::vector<RtlirImport> imports;

  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enum_types;
};

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;

  std::unordered_map<std::string_view, uint32_t> type_widths;
  // §6.18: "the type of the object is the type the name stands for", and the
  // width beside this cannot say what that is: EvalTypeWidth answers 0 for a
  // string, an event, a class handle and a type it could not size alike, so a
  // simulator asking the width alone cannot tell `typedef string s_t` from a
  // name it never saw. The resolved kind is recorded here for every name the
  // typedef table holds, chased through a chain of names to the kind at its
  // end, so the three declaration paths can ask what a name stands for rather
  // than reading DataType::kind and finding kNamed.
  std::unordered_map<std::string_view, DataTypeKind> type_kinds;
  // §6.11.1 makes byte, shortint, int, integer and longint signed by default,
  // and the `signed` keyword makes any of them signed explicitly; neither is
  // recoverable from the width or from the kind alone -- `logic signed [7:0]`
  // and `logic [7:0]` are one kind and one width. Recorded here for the same
  // reason and by the same walk, since a simulator asking IsSignedType of a
  // name has no typedef map to resolve it through.
  std::unordered_map<std::string_view, bool> type_signed;
  // §7.2.1: the resolved declaration of every packed struct or union a typedef
  // names. The three maps above say what a name stands for -- how wide, what
  // kind, signed or not -- and none of them says what is inside it, which is
  // what a member select of a value held under that type has to ask: `p.b`
  // names a run of bits of `p` and the offset of that run is a fact about
  // `pair_t`. A simulator has no typedef table to resolve the name through, and
  // the layout it does register is keyed by the name of a variable, so a value
  // held anywhere else -- a class property (§8.3) -- had nothing to ask at all.
  // Each entry is an arena-owned copy with its nested aggregate members
  // resolved, so it outlives the elaborator that built it.
  std::unordered_map<std::string_view, const DataType*> type_layouts;
  // §6.19 with §6.18: the enumeration declaration every typedef name standing
  // for an enumeration resolves to, under the typedef's key -- the bare name
  // for a module's or an imported one, "P::name" for a package's (§26.3) and
  // "C::name" for a class's (§8.23) -- as the elaborator's typedef table holds
  // it. §6.19.5 declares its methods on the enumeration type, and the
  // simulator, which registers a module's enumerations from RtlirModule's
  // enum_types alone, had no members to answer with for a property declared
  // with a class's or a package's typedef (RegisterDesignEnumTypes in
  // src/simulator/lowerer_data_init.cpp). Each entry is an arena-owned copy,
  // so it outlives the elaborator that built it; the member values fold in
  // the simulator against unit_constants below.
  std::unordered_map<std::string_view, const DataType*> type_enums;
  // §11.5.1 with §6.18: the packed range the type a name stands for was
  // declared with, as written, for the names standing for a vector of one
  // packed dimension whose bounds fold. `typedef bit [15:10] value_t` is six
  // bits wide, and the width alone addresses it as [5:0], so `v[13:10]` of a
  // `value_t v` declared inside a procedure or a subroutine body -- where the
  // declaration's DataType is the name and carries no dimension of its own --
  // read four bits that are outside a six-bit vector. Recorded only where the
  // bounds fold to constants and the type has one packed dimension; a name
  // nothing here records is addressed as [width-1:0], as before.
  std::unordered_map<std::string_view, PackedRange> type_ranges;
  // §6.18 with §8.3: the name at the end of the chain of typedefs a name
  // stands for, recorded for the names whose chain ends in a name the typedef
  // table does not resolve -- a class. `typedef C T;` makes T the class C
  // (§8.25.1's default specialization for a parameterized C), and a simulator
  // that knows a class by its declared name alone has this to find the class
  // a typedef name denotes, for `T::p` and `T obj`.
  std::unordered_map<std::string_view, std::string_view> type_targets;
  // §3.12.1 with §6.20.4 and §26.3: the value of every constant a declaration
  // outside any module may name in a constant expression -- a localparam of
  // the compilation-unit scope under its bare name, a package's parameter
  // under its "package.name" key, which is the spelling a `pkg::name`
  // reference folds through, and a name an import of the unit made locally
  // visible under the bare name it was imported as. A class body written at
  // compilation-unit scope, or in a module, sizes a property's packed
  // dimension by such a constant, `logic [p::W-1:0] v`, and the simulator
  // folds that dimension from the class declaration with no scope of its own
  // to read the value from; this is that scope. The keys are the parser's or
  // the elaborator's arena-owned strings, so they outlive the elaborator.
  std::unordered_map<std::string_view, int64_t> unit_constants;

  // §32.4.4: the parsed compilation unit and the top module declarations this
  // design was elaborated from. An interconnect delay is annotated between
  // module ports rather than onto a declaration, so what an SDF INTERCONNECT,
  // PORT or NETDELAY entry names is looked up in the design's own hierarchy of
  // ports, nets and primitives; CollectInterconnectTopology
  // (src/simulator/specify_sdf.h) reads that hierarchy off the AST, and a
  // lowered design has no other route back to it.
  const CompilationUnit* compilation_unit = nullptr;
  std::vector<const ModuleDecl*> top_decls;

  std::vector<ModuleItem*> cu_function_decls;

  std::vector<ModuleItem*> cu_let_decls;

  std::vector<PackageDecl*> packages;

  std::vector<ClassDecl*> cu_class_decls;

  // §20.4.1: the compilation unit's time unit and precision, reported by
  // $timeunit/$timeprecision when the $unit argument is supplied.
  TimeScale cu_timescale;

  // §3.14.3 / §20.4.1: the simulation time unit (the smallest time precision
  // across the design), reported by $timeunit/$timeprecision with $root.
  TimeUnit global_time_precision = TimeUnit::kNs;

  // §20.10.1: set when a $fatal or $error elaboration severity task is
  // executed. Simulation shall not be started against a design whose
  // elaboration tripped one of those severity levels.
  bool simulation_blocked = false;

  // §20.10.1: details of the most recent elaboration severity task that
  // executed. last_elab_severity is one of "FATAL", "ERROR", "WARNING",
  // "INFO"; empty when no task ran. last_elab_severity_loc carries the
  // file/line of the call (per §22.13's `__FILE__`/`__LINE__` pairing);
  // last_elab_severity_scope carries the hierarchical scope name; and
  // last_elab_severity_msg carries the user-defined message body.
  std::string last_elab_severity;
  std::string last_elab_severity_msg;
  std::string last_elab_severity_scope;
  SourceLoc last_elab_severity_loc;
};

}  // namespace delta
