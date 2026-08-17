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
  uint64_t decay_ticks = 0;

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

// The name prefix of the generate block instance a process or continuous
// assignment belongs to, empty outside any generate construct. A generate
// block "comprises a separate scope and a new level of hierarchy when it is
// instantiated" (§27.4), and declarations in that scope are named under this
// prefix, while the shared body AST still refers to them by their simple
// names. Carrying the prefix is what lets a reference from inside the block
// reach the instance's own declaration.
using GenBlockPrefix = std::string_view;

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
  GenBlockPrefix gen_block_prefix;
};

struct RtlirAlias {
  std::vector<Expr*> nets;
};

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  // Where the keyword that opened this procedure stands. A report that rejects
  // the procedure itself rather than a statement within it has no other
  // position to name: body is a separate statement carrying its own.
  SourceLoc loc;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
  GenBlockConsts gen_block_consts;
  GenBlockPrefix gen_block_prefix;
};

struct RtlirParamDecl {
  std::string_view name;
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
  std::vector<RtlirAlias> aliases;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  std::vector<ModuleItem*> function_decls;
  std::vector<ModuleItem*> let_decls;
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
