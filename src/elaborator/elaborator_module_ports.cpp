#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// Diagnose repeated explicitly-named (.name) ports within a single non-ANSI
// header.
static void CheckDuplicateExplicitPortNames(const ModuleDecl* decl,
                                            DiagEngine& diag) {
  std::unordered_set<std::string_view> explicit_names;
  for (const auto& port : decl->ports) {
    if (port.is_explicit_named && !port.name.empty()) {
      if (!explicit_names.insert(port.name).second) {
        diag.Error(port.loc,
                   std::format("duplicate port name '.{}'", port.name),
                   Subclause("23.2.2.1"));
      }
    }
  }
}

// Diagnose repeated ordinary port names in an ANSI header, tracked across the
// run via ansi_port_names.
static void CheckDuplicateAnsiPortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) {
      if (!ansi_port_names.insert(port.name).second) {
        diag.Error(port.loc, std::format("duplicate port name '{}'", port.name),
                   Subclause("23.2.2.2"));
      }
    }
  }
}

// Diagnose repeated port names: explicitly named (.name) ports in a non-ANSI
// header, and ordinary port names in an ANSI header (tracked across the run via
// ansi_port_names).
static void CheckDuplicatePortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  if (decl->is_non_ansi_ports) {
    CheckDuplicateExplicitPortNames(decl, diag);
  } else {
    CheckDuplicateAnsiPortNames(decl, ansi_port_names, diag);
  }
}

// §23.2.2: validate the contexts in which a port default value may appear —
// input ports only, ANSI-style declarations only, and singular non-interconnect
// types only.
static void ValidatePortDefaultValue(const PortDecl& port, bool is_non_ansi,
                                     const TypedefMap& typedefs,
                                     DiagEngine& diag) {
  if (port.direction != Direction::kInput) {
    // An output never reaches here: ValidatePortAssignment settles its
    // expression as an initializer, so the direction is inout or ref.
    diag.Error(
        port.loc,
        std::format("default value on {} port '{}'; defaults are "
                    "only allowed on input ports",
                    port.direction == Direction::kInout ? "inout" : "ref",
                    port.name),
        Subclause("23.2.2.4"));
  }
  if (is_non_ansi) {
    diag.Error(port.loc,
               std::format("default value on port '{}'; defaults are "
                           "only allowed with ANSI-style port "
                           "declarations",
                           port.name),
               Subclause("23.2.2.4"));
  }
  if (port.data_type.is_interconnect) {
    diag.Error(
        port.loc,
        std::format("default value on interconnect port '{}'", port.name),
        Subclause("23.2.2.4"));
  }
  if (!port.unpacked_dims.empty() ||
      !IsSingularType(port.data_type, typedefs)) {
    diag.Error(
        port.loc,
        std::format("default value on non-singular port '{}'", port.name),
        Subclause("23.2.2.4"));
  }
}

// §23.2.2.2's Syntax 23-4 writes `[ = constant_expression ]` behind a port's
// identifier, and its footnote 2 says which port each reading belongs to: only
// a variable output port may be initialized and only an input port may take a
// default value, which A.10 item 2 repeats. On a variable output port the
// expression is the port's initializer and is legal as written; on an output
// that is a net it is an initialization of a port that is no variable, reported
// here; on every other port it is the §23.2.2.4 default value
// ValidatePortDefaultValue holds to the input port.
static void ValidatePortAssignment(const PortDecl& port, bool port_is_var,
                                   bool is_non_ansi, const TypedefMap& typedefs,
                                   DiagEngine& diag) {
  if (port.direction != Direction::kOutput) {
    ValidatePortDefaultValue(port, is_non_ansi, typedefs, diag);
    return;
  }
  if (port_is_var) return;
  diag.Error(port.loc,
             std::format("initializer on output port '{}', which is a net and "
                         "no variable; only a variable output port may be "
                         "initialized",
                         port.name),
             Subclause("23.2.2.2"));
}

// The address range and the element count of every unpacked dimension of a
// port, and the number of dimensions the declaration wrote. The count is what
// the declaration says rather than what folded, so a consumer reading fewer
// ranges than dimensions knows a dimension went unrecorded rather than reading
// the port as one that is not an array.
static void ComputePortUnpackedDims(const PortDecl& port, RtlirPort& rp,
                                    const ScopeMap& scope, DiagEngine& diag) {
  for (auto* dim : port.unpacked_dims) {
    // §7.5 writes a dynamic array dimension as an empty pair of brackets, which
    // Parser::ParseUnpackedDims records as a null expression. It declares no
    // fixed size and no address range, so there is nothing here to fold and
    // nothing to report.
    if (dim == nullptr) continue;
    auto folded = FoldUnpackedDimBounds(dim, scope);
    if (!folded) {
      diag.Error(port.loc,
                 std::format("unpacked dimension of port '{}' is not a "
                             "constant expression",
                             port.name),
                 Subclause("7.4.2"));
      continue;
    }
    rp.unpacked_dims.push_back(*folded);
    rp.unpacked_dim_sizes.push_back(folded->Size());
  }
  rp.num_unpacked_dims = static_cast<uint32_t>(port.unpacked_dims.size());
}

// Reject port types that may never appear on a port (chandle, virtual
// interface). Emits the diagnostic and returns true when the port must be
// skipped.
static bool RejectIllegalPortType(const PortDecl& port, DiagEngine& diag) {
  if (port.data_type.kind == DataTypeKind::kChandle) {
    diag.Error(port.loc, "chandle cannot be used as a port type",
               Subclause("6.14"));
    return true;
  }
  if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
    diag.Error(port.loc, "virtual interface cannot be used as a port type",
               Subclause("25.9"));
    return true;
  }
  return false;
}

// §23.2.2: diagnose a non-ANSI port that appears in the header but never gets a
// direction declaration in the module body.
static void DiagnoseMissingNonAnsiPortDirection(const PortDecl& port,
                                                bool is_non_ansi,
                                                DiagEngine& diag) {
  if (is_non_ansi && !port.name.empty() && !port.is_explicit_named &&
      port.direction == Direction::kNone) {
    diag.Error(port.loc,
               std::format("port '{}' has no direction declaration in the "
                           "module body",
                           port.name),
               Subclause("23.2.2.1"));
  }
}

// §23.2.2.1: validate the per-port type constraints that do not block building
// the RtlirPort: interconnect ports may not be signed, and inout ports may not
// carry a variable data type.
static void DiagnosePortTypeConstraints(const PortDecl& port, bool port_is_var,
                                        DiagEngine& diag) {
  // Interconnect is an untyped generic connection, so it carries no signedness
  // of its own.
  if (port.data_type.is_interconnect && port.data_type.is_signed) {
    diag.Error(port.loc,
               std::format("interconnect port '{}' shall not be declared "
                           "signed",
                           port.name),
               Subclause("23.2.2.3"));
  }
  if (port.direction == Direction::kInout && port_is_var) {
    diag.Error(port.loc,
               std::format("variable data type is not permitted on "
                           "inout port '{}'",
                           port.name),
               Subclause("23.3.3.2"));
  }
}

// Which data types the §6.7.1 net rules admit for a net: item a of that clause
// names a 4-state integral type and item b an unpacked aggregate of valid net
// types, so an integral or aggregate data type is one a net may have. A checker
// formal of any other type -- an event, a string, a real -- holds its actual as
// a variable does (§17.2).
static bool PortDataTypeIsJudgedByNetRules(const DataType& dtype) {
  return IsIntegralType(dtype.kind) || dtype.kind == DataTypeKind::kStruct ||
         dtype.kind == DataTypeKind::kUnion;
}

// State threaded into ElaborateOnePort that would otherwise be Elaborator
// members; grouped so the helper can stay a free function (no header change).
// The non-ANSI port-tracking sets and the type-lookup context together form the
// elaboration state for one module's port list, so they travel as one object.
struct PortElabContext {
  const TypedefMap& typedefs;
  const ScopeMap& param_scope;
  std::unordered_set<std::string_view>& complete_ports;
  std::unordered_map<std::string_view, uint32_t>& partial_ports;
  std::unordered_set<std::string_view>& signed_ports;
  DiagEngine& diag;
  // The arena the resolved aggregate type of a structure port is copied into,
  // and the module the port's variable is declared on.
  Arena& arena;
  RtlirModule* mod;
};

// The resolved aggregate a structure or union port carries for its layout,
// the one ResolvedAggregateType lays out for a body declaration of the same
// type. §26.4 applies a header import before the port list, so a package's
// structure resolves here as the module's own does. Null for a port
// of any other type, and for the ports the layout is not for: a port with an
// unpacked or a use-site packed dimension is an array of the aggregate rather
// than one and keeps the width alone; a checker's formal is §17.2's, an
// expression substituted at the instance rather than an object of the checker;
// an explicitly named port is the expression it names; a non-ANSI port's body
// declaration carries its own layout (§23.2.2.1).
static const DataType* ResolvedPortAggregate(const ModuleDecl* decl,
                                             const PortDecl& port,
                                             const RtlirPort& rp,
                                             const PortElabContext& ctx) {
  if (decl->is_non_ansi_ports || decl->decl_kind == ModuleDeclKind::kChecker ||
      rp.is_interface_port || port.name.empty() || port.port_expr != nullptr ||
      !port.unpacked_dims.empty() ||
      port.data_type.packed_dim_left != nullptr ||
      !port.data_type.extra_packed_dims.empty()) {
    return nullptr;
  }
  return ResolvedAggregateType(port.data_type, ctx.typedefs, ctx.arena);
}

// §7.2.1 with §23.2.2.2: a variable port whose data type is a structure or a
// union is a variable of that aggregate, and a member select of it,
// `r.opcode`, names the run of the variable's bits the type lays the member
// out at. The port record carries the port's width, and an ANSI port has no
// body declaration to carry a layout either, so the simulator created the
// port's storage with no members to select. The port therefore declares the
// variable a body declaration of the same name declares for a non-ANSI port
// (§23.2.2.1), carrying the resolved aggregate for its layout; the simulator
// finds the storage already created under the port's name and keeps it as the
// port.
static void DeclareAggregatePortVariable(const PortDecl& port,
                                         const RtlirPort& rp,
                                         const DataType* aggregate,
                                         const PortElabContext& ctx) {
  RtlirVariable var;
  var.name = port.name;
  // §37.3.3: the variable stands where the port declaration does.
  var.loc = port.loc;
  var.width = rp.width;
  var.is_4state = Is4stateType(port.data_type, ctx.typedefs);
  var.is_signed = IsSignedType(port.data_type, ctx.typedefs);
  // §23.2.2.2, footnote 2: a variable output port's initializer is the value
  // the variable holds before any procedure runs, as a declaration's is.
  var.init_expr = rp.init_value;
  var.elem_type_kind = port.data_type.kind;
  var.decl_kind = port.data_type.kind;
  var.dtype = aggregate;
  ctx.mod->variables.push_back(var);
}

// Gives a structure or union port the layout a member select of it resolves
// against. §23.2.2.3 makes an input or inout port with no port kind a net of
// the default net type, `input instruction_t a` among them, and §6.7.1 admits
// a packed structure as a net's data type, its own example declaring `wire
// struct packed {...} memsig`. Such a port is a net -- its drivers resolve
// against each other and it carries a strength (§28.12) -- so it declares no
// variable; the resolved aggregate travels on the port record instead, which
// is the type the header declared, and the simulator lays the net's storage
// out from it when it creates the port. A variable port declares the variable
// above. Declaring a variable for the net port too would have made the port
// the variable the simulator finds first, and a net no longer.
static void LayOutAggregatePort(const ModuleDecl* decl, const PortDecl& port,
                                RtlirPort& rp, const PortElabContext& ctx) {
  const DataType* aggregate = ResolvedPortAggregate(decl, port, rp, ctx);
  if (aggregate == nullptr) return;
  if (rp.is_var) {
    DeclareAggregatePortVariable(port, rp, aggregate, ctx);
    return;
  }
  rp.dtype = aggregate;
}

// §23.2.2.3: a port whose port kind was omitted is a net of the default net
// type for input and inout, and for output when the data type was omitted or
// written with the implicit_data_type syntax. Such a port is a net, and §6.7.1
// restricts what data type a net may have, so the rule that governs a net
// declaration reaches the port spelling too. A port that is a variable is
// outside that rule and keeps every data type it could have.
//
// The rule is read off §23.2.2 "Port declarations", which is about the ports of
// a module, an interface and a program. A checker's formal arguments are
// §17.2's, where a formal may be left untyped altogether and nothing describes
// one as a net, so a checker is not put under this rule here.
static void ValidateNetPortDataType(const ModuleDecl* decl,
                                    const PortDecl& port, bool port_is_var,
                                    const PortElabContext& ctx) {
  if (decl->decl_kind == ModuleDeclKind::kChecker) return;
  if (port_is_var) return;
  ValidateNetDataTypeIs4State(port.data_type, ctx.typedefs, ctx.diag, port.loc);
}

// Record the type information of a directioned non-ANSI port so the matching
// body net/variable declaration can be reconciled later (§23.2.2.1). The
// tracking sets are reference members of the context, so a const reference
// still allows recording into them.
static void TrackNonAnsiPortType(const ModuleDecl* decl, const PortDecl& port,
                                 const PortElabContext& ctx) {
  if (!decl->is_non_ansi_ports || port.name.empty() ||
      port.direction == Direction::kNone) {
    return;
  }
  if (port.data_type.kind != DataTypeKind::kImplicit) {
    ctx.complete_ports.insert(port.name);
  } else {
    ctx.partial_ports[port.name] =
        EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
    // §23.2.2.1: remember a `signed` port direction declaration so the
    // matching net/variable declaration can be considered signed too.
    if (port.data_type.is_signed) ctx.signed_ports.insert(port.name);
  }
}

// The bits a port written as a select of a declared vector names, `a[7:4]` of
// a non-ANSI header being four, or 0 where the port is no select whose bounds
// fold.
static uint32_t SelectPortWidth(const Expr* expr, const ScopeMap& scope) {
  if (expr->kind != ExprKind::kSelect) return 0;
  if (expr->index_end == nullptr) return 1;
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    auto w = ConstEvalInt(expr->index_end, scope);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto left = ConstEvalInt(expr->index, scope);
  auto right = ConstEvalInt(expr->index_end, scope);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

// Fill the base (non-interface) fields of an RtlirPort from its declaration,
// including the folded unpacked-dimension sizes.
static RtlirPort BuildRtlirPortBase(const PortDecl& port, bool port_is_var,
                                    uint32_t width, const ScopeMap& scope,
                                    DiagEngine& diag) {
  RtlirPort rp;
  rp.name = port.name;
  // §23.2.2.1: a named port connection may reach an implicit port only when its
  // port expression is a simple (or escaped) identifier, which serves as the
  // port name. An implicit port written as a bit-select, part-select, or
  // concatenation has no port name and must not be name-connectable. A
  // concatenation already parses with no name; a select port otherwise retains
  // its base identifier, so drop that name here to keep it order-only.
  if (!port.is_explicit_named && port.port_expr != nullptr) rp.name = {};
  rp.direction = port.direction;
  rp.type_kind = port.data_type.kind;
  rp.width = width;
  // §23.2.2.1 (printed page 732), Example 3: `split_ports (a[7:4], a[3:0])`
  // makes the first port a's upper four bits and the second its lower four.
  // Such a port is its select of the declared vector, four bits wide, and its
  // connection is joined to that select (LowerPortBindings); taken as the whole
  // of a, with no name to find storage by, it connected nothing.
  if (!port.is_explicit_named && port.port_expr != nullptr) {
    rp.port_expr = port.port_expr;
    if (uint32_t w = SelectPortWidth(port.port_expr, scope); w > 0) {
      rp.selected_width = width;
      rp.width = w;
    }
  }
  // §11.5.1: the width above says how many bits the port has, not which bit an
  // index names. Carry the declared type wherever the port header holds a
  // packed dimension, so a select on the port can be resolved over the range as
  // written -- the same condition ElaborateNetDecl applies to a net's own
  // declaration. `port` is an element of ModuleDecl::ports, which the parser
  // fills and no elaboration step appends to, so the DataType outlives the
  // RtlirPort built from it.
  if (port.data_type.packed_dim_left != nullptr ||
      !port.data_type.extra_packed_dims.empty()) {
    rp.dtype = &port.data_type;
  }
  rp.is_signed = port.data_type.is_signed;
  rp.is_var = port_is_var;
  rp.is_interconnect = port.data_type.is_interconnect;
  // §23.2.2.3: where a port names no net type, ElaborateOnePort puts the
  // default net type in place of the wire WrittenNetType answers.
  if (!port_is_var) rp.net_type = WrittenNetType(port.data_type);
  // Syntax 23-4's one `= constant_expression` is an initializer on a variable
  // output port and a default value on an input port (§23.2.2.2, footnote 2),
  // so each kind of port carries it in the field its readers look in: the
  // instantiation that leaves an input unconnected reads default_value, and
  // the simulator's port variable takes init_value; an output that is no
  // variable was reported and carries neither.
  if (port.direction == Direction::kOutput) {
    if (port_is_var) rp.init_value = port.default_value;
  } else {
    rp.default_value = port.default_value;
  }
  ComputePortUnpackedDims(port, rp, scope, diag);
  return rp;
}

// Elaborate one port declaration into its RtlirPort: run the per-port
// diagnostics, track non-ANSI type info, and build the base fields. The
// interface-port flag is resolved by the caller because it needs FindModule.
static RtlirPort ElaborateOnePort(const ModuleDecl* decl, const PortDecl& port,
                                  PortElabContext& ctx) {
  DiagnoseMissingNonAnsiPortDirection(port, decl->is_non_ansi_ports, ctx.diag);
  TrackNonAnsiPortType(decl, port, ctx);

  // §17.2: a checker formal is no port, and one of a type §6.7.1 gives no
  // net -- a string, a real, an event -- holds its actual as a variable does.
  bool port_is_var =
      (!port.data_type.is_net && !port.data_type.is_interconnect) ||
      (decl->decl_kind == ModuleDeclKind::kChecker &&
       !PortDataTypeIsJudgedByNetRules(port.data_type));
  if (port.default_value) {
    ValidatePortAssignment(port, port_is_var, decl->is_non_ansi_ports,
                           ctx.typedefs, ctx.diag);
  }

  DiagnosePortTypeConstraints(port, port_is_var, ctx.diag);
  ValidateNetPortDataType(decl, port, port_is_var, ctx);

  uint32_t width = EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
  RtlirPort rp =
      BuildRtlirPortBase(port, port_is_var, width, ctx.param_scope, ctx.diag);
  rp.data_kind = ResolvedTypeKind(port.data_type, ctx.typedefs);
  // §23.2.2.3: a port whose port kind is omitted defaults to a net of the
  // default net type, the one in force where the module is defined (§22.8). A
  // module under `default_nettype none has no default net type to give, so its
  // port keeps the wire; a checker's formals are no ports (§17.2).
  if (decl->decl_kind != ModuleDeclKind::kChecker && !port_is_var &&
      !port.data_type.is_interconnect &&
      port.data_type.net_keyword == DataTypeKind::kImplicit &&
      DataTypeToNetType(port.data_type.kind) == NetType::kWire &&
      ctx.mod->default_nettype != NetType::kNone) {
    rp.net_type = ctx.mod->default_nettype;
  }
  return rp;
}

// 23.2.2.4: a default input-port value is a constant expression evaluated in
// the scope of the module where the port is defined, not in the scope of the
// instantiating module. Fold it against this module's parameter scope (which
// already includes the compilation-unit scope and any per-instance parameter
// overrides) and capture the resolved constant as a literal, so it is not
// re-resolved in the instantiating scope when later used as a port connection.
static void FoldPortConstant(Arena& arena, const ScopeMap& scope,
                             Expr*& value) {
  if (value == nullptr) return;
  // A literal is already scope-independent, so leave it untouched; this also
  // avoids truncating a wide (>64-bit) literal through the 64-bit fold, a
  // string literal of more than eight characters among them (§5.9). Only
  // name-bearing expressions need to be pinned to the defining scope.
  if (value->kind == ExprKind::kIntegerLiteral ||
      value->kind == ExprKind::kStringLiteral) {
    return;
  }
  auto v = ConstEvalInt(value, scope);
  if (!v) return;
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(*v);
  value = lit;
}

// A variable output port's initializer is a constant_expression of the same
// scope (§23.2.2.2), so it is folded the same way for the simulator to read.
static void FoldPortDefaultValue(Arena& arena, const ScopeMap& scope,
                                 RtlirPort& rp) {
  FoldPortConstant(arena, scope, rp.default_value);
  FoldPortConstant(arena, scope, rp.init_value);
}

// §23.2.3: port declarations can be based on parameter declarations. In the
// non-ANSI header style the parameters are ordinary module_items in the body
// (e.g. `parameter MSB = 3; input [MSB:LSB] in;`), and those items are only
// fully elaborated after the ports. Fold each body value parameter into the
// port-sizing scope in declaration order so a port packed range that references
// one resolves to the parameter's value rather than defaulting to a scalar.
// Header (parameter_port_list) parameters are already in `scope` via
// BuildParamScope; type parameters have no integer value and fall out because
// their init expression does not fold to an integer.
static void FoldBodyParamsIntoPortScope(const ModuleDecl* decl,
                                        ScopeMap& scope) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl ||
        item->init_expr == nullptr || item->name.empty()) {
      continue;
    }
    if (auto val = ConstEvalInt(item->init_expr, scope))
      scope[item->name] = *val;
  }
}

// Whether the module's body declares `name` as a net or a variable of its own.
static bool BodyDeclaresObject(const ModuleDecl* decl, std::string_view name) {
  return std::any_of(decl->items.begin(), decl->items.end(),
                     [&](const ModuleItem* item) {
                       return (item->kind == ModuleItemKind::kNetDecl ||
                               item->kind == ModuleItemKind::kVarDecl) &&
                              item->name == name;
                     });
}

// §6.6.8: an interconnect port is a typeless/generic net, exactly like a
// local interconnect declaration. Register its name so the assignment- and
// expression-use checks -- which reject procedural/continuous/expression uses
// of an interconnect net or port -- also fire for the port inside its own
// module. A non-ANSI interconnect port already registers via its body net
// declaration; this covers the ANSI `interconnect p` header form.
//
// §23.2.2.3: a port the clause makes a net of the default net type -- `output
// b` with no port kind and no data type among them, the clause's own `mh8
// (output x)` -- is likewise a net to every rule of its module that asks
// whether a name is one, §10.4's rule that a procedural assignment's left-hand
// side be a variable first. Left out of net_names_, `b <= a` in an always_ff
// on such a port was accepted, the suite's
// 14.3--clocking-block-signals-error.sv with it, while the same write to a
// declared `wire w` was reported. A non-ANSI port the body declares again is
// that declaration's object (§23.2.2.1), which registers itself if it is a
// net, so only a non-ANSI port the body leaves undeclared registers here; a
// checker's formal is §17.2's and no net.
static void RegisterPortNetNames(
    const ModuleDecl* decl, const PortDecl& port, const RtlirPort& rp,
    std::unordered_set<std::string_view>& interconnect_names,
    std::unordered_set<std::string_view>& net_names) {
  if (port.name.empty()) return;
  if (port.data_type.is_interconnect) interconnect_names.insert(port.name);
  if (decl->decl_kind == ModuleDeclKind::kChecker || rp.is_var) return;
  if (decl->is_non_ansi_ports && BodyDeclaresObject(decl, port.name)) return;
  net_names.insert(port.name);
}

// §23.2.2.1 (printed page 733), Example 5: `renamed_concat(.a({b, c}), f,
// .g(h[1]))` with `input b, c;` and `output [1:0] h;` in the body, where b, c
// and h are no ports but the objects the ports a and g stand for. Each is
// declared as its port declaration makes it -- a net of the default net type
// for `input b`, a variable for `output reg h` -- unless the body declares it
// again as a net or a variable, which then gives it its storage. Dropped, the
// declarations left b, c and h undeclared inside the module.
static void DeclarePortExprObjects(const ModuleDecl* decl, RtlirModule* mod,
                                   PortElabContext& ctx) {
  for (const PortDecl& obj : decl->port_expr_objects) {
    if (BodyDeclaresObject(decl, obj.name)) continue;
    RtlirPort rp = ElaborateOnePort(decl, obj, ctx);
    if (rp.net_type != NetType::kNone) {
      RtlirNet net;
      net.name = obj.name;
      net.loc = obj.loc;
      net.net_type = rp.net_type;
      net.width = rp.width;
      net.dtype = rp.dtype;
      net.is_signed = rp.is_signed;
      mod->nets.push_back(net);
      continue;
    }
    RtlirVariable var;
    var.name = obj.name;
    var.loc = obj.loc;
    var.width = rp.width;
    var.is_signed = rp.is_signed;
    var.is_4state = Is4stateType(obj.data_type, ctx.typedefs);
    var.dtype = rp.dtype;
    mod->variables.push_back(var);
  }
}

// The direction of the object a port expression names first, `b` of
// `{b, c}` and `h` of `h[1]`, as its body port declaration gives it;
// Direction::kNone where the expression names none of them.
static Direction PortExprDirection(const ModuleDecl* decl, const Expr* expr) {
  while (expr != nullptr && expr->kind == ExprKind::kSelect) expr = expr->base;
  if (expr == nullptr) return Direction::kNone;
  if (expr->kind == ExprKind::kConcatenation) {
    return expr->elements.empty() ? Direction::kNone
                                  : PortExprDirection(decl, expr->elements[0]);
  }
  if (expr->kind != ExprKind::kIdentifier) return Direction::kNone;
  for (const PortDecl& obj : decl->port_expr_objects) {
    if (obj.name == expr->text) return obj.direction;
  }
  return Direction::kNone;
}

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);
  FoldBodyParamsIntoPortScope(decl, param_scope);

  CheckDuplicatePortNames(decl, ansi_port_names_, diag_);

  PortElabContext ctx{typedefs_,
                      param_scope,
                      non_ansi_complete_ports_,
                      non_ansi_partial_ports_,
                      non_ansi_signed_ports_,
                      diag_,
                      arena_,
                      mod};

  DeclarePortExprObjects(decl, mod, ctx);
  for (const auto& port : decl->ports) {
    if (RejectIllegalPortType(port, diag_)) continue;

    RtlirPort rp = ElaborateOnePort(decl, port, ctx);
    // §23.2.2.1: a port of a non-ANSI header written as an expression faces
    // the way the body declares the objects it names, `.a({b, c})` and
    // `{c, d}` under `input b, c, d;` being inputs.
    if (port.port_expr != nullptr && rp.direction == Direction::kNone) {
      rp.direction = PortExprDirection(decl, port.port_expr);
    }
    RegisterPortNetNames(decl, port, rp, interconnect_names_, net_names_);
    // §37.3.3: where the port declaration stands, which the port object
    // reports through vpiLineNo and vpiFile.
    rp.loc = port.loc;
    FoldPortDefaultValue(arena_, param_scope, rp);

    if (port.is_interface_port) {
      rp.is_interface_port = true;
      // §23.3.3.4: a named interface-type port (`bus_if p` / `bus_if.mp p`)
      // records its required interface type so the connection check can reject
      // an instance of a different type. A generic `interface p` port leaves
      // type_name empty, so it keeps accepting any interface instance.
      rp.interface_type_name = port.data_type.type_name;
    } else if (port.direction == Direction::kNone &&
               port.data_type.kind == DataTypeKind::kNamed &&
               !port.data_type.type_name.empty()) {
      auto* ifc_decl = FindModule(port.data_type.type_name);
      if (ifc_decl && ifc_decl->decl_kind == ModuleDeclKind::kInterface) {
        rp.is_interface_port = true;
        rp.interface_type_name = port.data_type.type_name;
      }
    }

    LayOutAggregatePort(decl, port, rp, ctx);
    mod->ports.push_back(rp);
  }
}

}  // namespace delta
