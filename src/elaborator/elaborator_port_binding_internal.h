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

namespace delta {

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

inline NetType FindSignalNetType(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.net_type;
  }
  return NetType::kNone;
}

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
  bool child_is_checker = false;
};

int NetTypeGroup(NetType t);
bool DissimilarNetResultIsInternal(NetType internal, NetType external);
NetType MergedInterconnectNetType(NetType merged, NetType incoming);
void CheckRefPortsConnected(DiagEngine& diag,
                            const std::vector<RtlirPort>& child_ports,
                            const RtlirModuleInst& inst,
                            const ModuleItem* item);
std::string_view ConnectedInterfaceName(const Expr* conn);
std::string_view ResolveConnectedInterfaceType(const PortBindCtx& ctx,
                                               std::string_view conn_name,
                                               bool& found);
void CheckInterfacePortsConnected(const PortBindCtx& ctx,
                                  const std::vector<RtlirPort>& child_ports,
                                  const RtlirModuleInst& inst);

void CoerceDrivenInputPorts(RtlirModuleInst& inst, const RtlirModule* parent);

bool ImportBringsInSignal(const RtlirModule* mod, const CompilationUnit* unit,
                          std::string_view name, bool wildcard_counts);

bool PortAndSignalDiffer(const RtlirPort& port, std::string_view name,
                         const RtlirModule* parent);

void ReportNonEquivalentImplicitConnection(DiagEngine& diag, SourceLoc loc,
                                           bool is_wildcard,
                                           const RtlirPort& port,
                                           const RtlirModule* parent);

void ReportVariableOnInout(const PortBindCtx& ctx, std::string_view name,
                           std::string_view port_name, bool port_is_var);

void CheckInoutConnectionParts(const PortBindCtx& ctx, const Expr* conn_expr,
                               const RtlirPort& port,
                               std::string_view port_name);

}  // namespace delta
