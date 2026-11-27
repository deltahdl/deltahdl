#include "elaborator/chandle_ports.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr std::string_view kChandlePort =
    "chandle cannot be used as a port type";

bool TypeHoldsChandle(const DataType& dtype, const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, typedefs, names);
  if (type == nullptr) return false;
  if (type->kind == DataTypeKind::kChandle) return true;
  return std::ranges::any_of(
      type->struct_members, [&](const StructMember& member) {
        const DataType* own = MemberOwnType(member, typedefs);
        return own != nullptr ? TypeHoldsChandle(*own, typedefs)
                              : member.type_kind == DataTypeKind::kChandle;
      });
}

bool ModportPortNamesChandle(const ModuleDecl& decl, const ModportPort& port,
                             const TypedefMap& typedefs) {
  return std::ranges::any_of(decl.items, [&](const ModuleItem* item) {
    return item->kind == ModuleItemKind::kVarDecl && item->name == port.name &&
           TypeHoldsChandle(item->data_type, typedefs);
  });
}

}  // namespace

void ReportChandlePorts(const ModuleDecl& decl, const TypedefMap& typedefs,
                        DiagEngine& diag) {
  for (const PortDecl& port : decl.ports) {
    if (TypeHoldsChandle(port.data_type, typedefs)) {
      diag.ErrorOnce(port.loc, std::string(kChandlePort), Subclause("6.14"));
    }
  }
  for (const ModportDecl* modport : decl.modports) {
    for (const ModportPort& port : modport->ports) {
      if (ModportPortNamesChandle(decl, port, typedefs)) {
        diag.ErrorOnce(modport->loc, std::string(kChandlePort),
                       Subclause("6.14"));
      }
    }
  }
}

}  // namespace delta
