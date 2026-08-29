#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast.h"

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
  // declares a packed dimension; null otherwise, which leaves the port
  // addressed as [0:0].
  const DataType* dtype = nullptr;

  bool is_var = false;
  bool is_interconnect = false;
  bool is_interface_port = false;
  std::string_view interface_type_name;
  Expr* default_value = nullptr;
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
  // the range as written; null for a scalar, which is addressed as [0:0].
  const DataType* dtype = nullptr;

  bool is_signed = false;
  std::vector<uint32_t> driver_indices;

  Strength charge_strength = Strength::kMedium;
  uint32_t trireg_capacitance = 0;

  // §28.16.2.2: the charge decay time of a trireg net, counted in time units,
  // which the declaration writes as its third delay: "The third delay in a
  // trireg net declaration shall specify the charge decay time." Zero records a
  // net that does not decay, which is what §28.16.2 leaves a trireg whose
  // declaration writes no third delay holding its charge with. Only a trireg
  // carries one, because §28.16.2 gives the third delay of every other net to
  // "the delay in a transition to the z logic state" instead.
  uint64_t decay_ticks = 0;

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
  std::string_view enum_type_name;
  std::vector<ResolvedAttribute> attrs;
};

// §27.4: the implicit localparam of every enclosing loop generate block -- "an
// integer parameter that has the same name and type as the loop index, and its
// value within each instance of the generate block is the value of the loop
// index at the time the instance was elaborated". Unrolling shares one body AST
// across the instances, so the per-instance values cannot live in the body;
// they ride on whatever the block elaborated to. Outermost enclosing loop
// first. Empty outside any loop generate construct.
using GenBlockConsts = std::vector<std::pair<std::string_view, int64_t>>;

// The name prefixes of the generate block instances enclosing a process or
// continuous assignment, outermost first, with the instance's own prefix last.
// Empty outside any generate construct. A generate block "comprises a separate
// scope and a new level of hierarchy when it is instantiated" (§27.4), and
// declarations in that scope are named under its prefix, while the shared body
// AST still refers to them by their simple names. Carrying the prefixes is what
// lets a reference from inside the block reach the instance's own declaration,
// and §23.9 is why every enclosing one comes too: the search for a name
// "referenced directly (without a hierarchical path) within a ... generate
// block" continues "upward until an item by that name is found or until a
// module, interface, program, or checker boundary is encountered". The
// innermost prefix flattens the whole path into one string, which no reader can
// split back into the steps that search needs.
using GenBlockPrefixes = std::vector<std::string_view>;

// §23.9: whether a parameter declared under `decl_prefix` -- the generate block
// prefix in force where it was written, which RtlirParamDecl::gen_block_prefix
// holds -- is visible to a reference standing in the generate blocks `scopes`.
// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// and rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree", so a block's parameter reaches that block and the
// blocks nested inside it and nothing else. A parameter of the module itself
// carries an empty prefix and is visible throughout the module.
//
// `scopes` holds the prefixes in force at the reference, outermost first. Pass
// an empty list where the reference has no position inside the module to speak
// of -- a reader answering about another module, or one reached through
// RegisteredModule(), which names a module and nothing about where inside it an
// expression stands -- which admits the module's own parameters alone.
inline bool ParamVisibleFromScopes(std::string_view decl_prefix,
                                   const GenBlockPrefixes& scopes) {
  if (decl_prefix.empty()) return true;
  for (std::string_view scope : scopes) {
    if (scope == decl_prefix) return true;
  }
  return false;
}

// §23.6: one step of a hierarchical path name, which Syntax 23-7 writes as
// `identifier constant_bit_select`. §23.6 forms such a name "by concatenating
// the names of the modules, module instance names, generate blocks, tasks,
// functions, assertion labels, named assertion action blocks, or named blocks
// that contain it", so a generate block instance is a step of one. §27.4
// indexes a loop generate block's instances "by adding the '[genvar value]' to
// the end of the generate block identifier", which is what `index` holds, and
// §23.6 requires the select "if the array name is not the last path element in
// the hierarchical name", so `has_index` distinguishes a loop generate block
// from a conditional one rather than merely recording whether one was written.
//
// A step of an unnamed generate block has an empty `name`. §27.6 gives such a
// block the name genblk<n>, but §23.6 rules that what it declares "can be
// referenced by hierarchical names only from within the block", and no written
// identifier is empty, so the step matches nothing a path outside can spell.
struct HierStep {
  std::string_view name;
  bool has_index = false;
  int64_t index = 0;
};

// §23.6: a hierarchical path name as a sequence of its steps. Two things are
// spelled this way. A path a source wrote ends in the object it names, and the
// generate block instances enclosing a declaration are the steps between its
// module and it, outermost first and empty for a declaration of the module
// itself. Comparing the two is what resolves the first, which the flattened
// name a declaration is stored under cannot do: `g_u` is what both `g.u` and a
// module-level instance named `g_u` are spelled as, and §23.6 makes them
// different scopes.
using HierPath = std::vector<HierStep>;

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
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
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
  int64_t resolved_value = 0;
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
  DelayModeDirective delay_mode = DelayModeDirective::kNone;

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
  std::vector<ModuleItem*> function_decls;
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
  std::vector<ClassDecl*> class_decls;
  std::vector<RtlirImport> imports;

  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enum_types;
};

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;

  std::unordered_map<std::string_view, uint32_t> type_widths;

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
