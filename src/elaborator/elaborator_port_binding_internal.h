#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

// Internal helpers shared between the port-binding translation units
// (elaborator_port_binding.cpp and elaborator_port_binding_checks.cpp). These
// implement §23.3.x instance port-binding/legality support and are not part of
// the public elaborator interface.
namespace delta {

// Width of the parent-scope signal named `name` (variable, net, or port), or 0
// when the name is not declared in `mod`.
inline uint32_t FindSignalWidth(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

// Net type of the parent-scope net named `name`, or kNone when `name` is not a
// net of `mod`.
inline NetType FindSignalNetType(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.net_type;
  }
  return NetType::kNone;
}

// Maps a net-kind data type to its NetType, or kNone for non-net (variable)
// port kinds.
inline NetType PortNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
      return NetType::kWire;
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kNone;
  }
}

// §23.3.3 per-instance port-binding context: the diagnostic sink and
// instantiation site errors report against, the instantiating module, and its
// signal classifications consulted by the connection checks.
struct PortBindCtx {
  DiagEngine& diag;
  const ModuleItem* item;
  const RtlirModule* parent_mod;
  const std::unordered_set<std::string_view>& nettype_net_names;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& interconnect_names;
  const std::unordered_map<std::string_view, std::string_view>&
      interface_inst_types;
  // §17.3: the instance is of a checker, whose formals take their actuals as
  // a sequence's or property's do rather than as a module's ports.
  bool child_is_checker = false;
};

int NetTypeGroup(NetType t);
bool DissimilarNetResultIsInternal(NetType internal, NetType external);
void CheckRefPortsConnected(DiagEngine& diag,
                            const std::vector<RtlirPort>& child_ports,
                            const RtlirModuleInst& inst,
                            const ModuleItem* item);
// The interface instance or interface port an interface port's actual names,
// or empty for an actual that names neither: an identifier, a modport of one,
// `i.mp`, and an element of an array of interface instances, `ia[0]`, which
// §23.3.3.4 connects as an interface instance (§23.3.2 makes each element of an
// array of instances an instance of its own), named by its array.
std::string_view ConnectedInterfaceName(const Expr* conn);
std::string_view ResolveConnectedInterfaceType(const PortBindCtx& ctx,
                                               std::string_view conn_name,
                                               bool& found);
void CheckInterfacePortsConnected(const PortBindCtx& ctx,
                                  const std::vector<RtlirPort>& child_ports,
                                  const RtlirModuleInst& inst);

// §23.3.3.1: an input net port the instance's module drives with a
// continuous assignment, connected to a net of `parent`, is coerced to inout.
// Defined in elaborator_port_binding_checks.cpp.
void CoerceDrivenInputPorts(RtlirModuleInst& inst, const RtlirModule* parent);

// §26.3: whether an import `mod` writes at its own level brings in a variable
// or a net named `name` from the package it names: an explicit import of the
// name, or -- where `wildcard_counts`, the reference asking being enough to
// import a candidate -- a wildcard import of a package declaring it. Defined in
// elaborator_port_binding_checks.cpp.
bool ImportBringsInSignal(const RtlirModule* mod, const CompilationUnit* unit,
                          std::string_view name, bool wildcard_counts);

// §6.22.2: whether the instantiating module's signal `name` and `port` differ
// in width, in signing or in their number of states, the facts that tell
// equivalent integral types apart. False where the module declares no such
// signal. Defined in elaborator_port_binding_checks.cpp.
bool PortAndSignalDiffer(const RtlirPort& port, std::string_view name,
                         const RtlirModule* parent);

// §23.3.2.3 and §23.3.2.4: the declarations either side of an implicit
// `.name` connection, or a `.*` one where `is_wildcard`, have equivalent data
// types, which §6.22.2 makes, for the integral types such a connection joins,
// the same width, the same signing and the same number of states; a mismatch
// is reported at `loc` under the subclause of the form.
// Defined in elaborator_port_binding_checks.cpp.
void ReportNonEquivalentImplicitConnection(DiagEngine& diag, SourceLoc loc,
                                           bool is_wildcard,
                                           const RtlirPort& port,
                                           const RtlirModule* parent);

}  // namespace delta
