#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

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
};

}  // namespace delta
