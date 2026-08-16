#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

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
    diag.Error(port.loc,
               std::format("default value on {} port '{}'; defaults are "
                           "only allowed on input ports",
                           port.direction == Direction::kOutput  ? "output"
                           : port.direction == Direction::kInout ? "inout"
                                                                 : "ref",
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

// Fold one unpacked dimension of a port into the address range it declares.
//
// §7.4.2 writes a fixed-size unpacked dimension as
// `[ constant_expression : constant_expression ]`, whose "first value may be
// greater than, equal to, or less than the second value", and admits the short
// form where "[size] shall mean the same as [0:size-1]". Both bounds are kept
// in the order written, because §11.5.2 resolves an address against "the
// address bounds given in the declaration" and `[1:4]` and `[4:1]` place their
// elements at the same addresses in opposite order.
//
// The bounds are folded in the port's own parameter scope. §11.2.1 lets a
// constant expression name a parameter, so `mem [N]` and `mem [1:N-1]` are
// dimensions the empty scope resolves nothing in, and a dimension that folds to
// nothing is one no consumer is told about.
static std::optional<RtlirUnpackedDim> FoldPortUnpackedDim(
    const Expr* dim, const ScopeMap& scope) {
  if (dim == nullptr) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs, scope);
    auto rv = ConstEvalInt(dim->rhs, scope);
    if (!lv || !rv) return std::nullopt;
    return RtlirUnpackedDim{*lv, *rv};
  }
  auto sv = ConstEvalInt(dim, scope);
  if (!sv || *sv <= 0) return std::nullopt;
  return RtlirUnpackedDim{0, *sv - 1};
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
    auto folded = FoldPortUnpackedDim(dim, scope);
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

// Which port data types the §6.7.1 net rules can decide. Item a of that clause
// judges "a 4-state integral type" and item b an unpacked aggregate whose
// elements are themselves valid net types, so an integral or aggregate data
// type is one the rule speaks about. A port naming an event, a string, a real,
// a chandle or an interface raises a prior question instead -- whether
// §23.2.2.3's "net of default net type" makes such a port a net at all -- and
// nothing here answers it, so those are left where they were. A net written as
// a net declaration is not in doubt that way and is judged in full.
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
};

// §23.2.2.3: a port whose port kind was omitted is "a net of default net type"
// for input and inout, and for output when the data type was omitted or
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
  if (port_is_var || !PortDataTypeIsJudgedByNetRules(port.data_type)) return;
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
  rp.default_value = port.default_value;
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

  if (port.default_value) {
    ValidatePortDefaultValue(port, decl->is_non_ansi_ports, ctx.typedefs,
                             ctx.diag);
  }

  bool port_is_var = !port.data_type.is_net && !port.data_type.is_interconnect;
  DiagnosePortTypeConstraints(port, port_is_var, ctx.diag);
  ValidateNetPortDataType(decl, port, port_is_var, ctx);

  uint32_t width = EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
  return BuildRtlirPortBase(port, port_is_var, width, ctx.param_scope,
                            ctx.diag);
}

// 23.2.2.4: a default input-port value is a constant expression evaluated in
// the scope of the module where the port is defined, not in the scope of the
// instantiating module. Fold it against this module's parameter scope (which
// already includes the compilation-unit scope and any per-instance parameter
// overrides) and capture the resolved constant as a literal, so it is not
// re-resolved in the instantiating scope when later used as a port connection.
static void FoldPortDefaultValue(Arena& arena, const ScopeMap& scope,
                                 RtlirPort& rp) {
  if (rp.default_value == nullptr) return;
  // A literal default is already scope-independent, so leave it untouched; this
  // also avoids truncating a wide (>64-bit) literal through the 64-bit fold.
  // Only name-bearing expressions need to be pinned to the defining scope.
  if (rp.default_value->kind == ExprKind::kIntegerLiteral) return;
  auto v = ConstEvalInt(rp.default_value, scope);
  if (!v) return;
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(*v);
  rp.default_value = lit;
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

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);
  FoldBodyParamsIntoPortScope(decl, param_scope);

  CheckDuplicatePortNames(decl, ansi_port_names_, diag_);

  PortElabContext ctx{typedefs_,
                      param_scope,
                      non_ansi_complete_ports_,
                      non_ansi_partial_ports_,
                      non_ansi_signed_ports_,
                      diag_};

  for (const auto& port : decl->ports) {
    if (RejectIllegalPortType(port, diag_)) continue;

    // §6.6.8: an interconnect port is a typeless/generic net, exactly like a
    // local interconnect declaration. Register its name so the assignment- and
    // expression-use checks — which reject procedural/continuous/expression
    // uses of an interconnect "net or port" — also fire for the port inside its
    // own module. A non-ANSI interconnect port already registers via its body
    // net declaration; this covers the ANSI `interconnect p` header form.
    if (port.data_type.is_interconnect && !port.name.empty())
      interconnect_names_.insert(port.name);

    RtlirPort rp = ElaborateOnePort(decl, port, ctx);
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

    mod->ports.push_back(rp);
  }
}

}  // namespace delta
