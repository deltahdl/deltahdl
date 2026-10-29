#include "elaborator/net_or_variable_type.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>

#include "elaborator/expression_self_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §6.7.1: a net declared with no data type, its kind the net type's keyword,
// and a declaration writing only a signing or a range are of logic.
static DataType OfLogicWhereImplicit(DataType type) {
  if (type.kind == DataTypeKind::kImplicit || IsNetTypeKind(type.kind))
    type.kind = DataTypeKind::kLogic;
  return type;
}

// §23.2.2.3: the net the port `name` of `decl` declares.
static std::optional<DeclaredValue> PortNetValue(std::string_view name,
                                                 const ModuleDecl* decl) {
  if (decl == nullptr) return std::nullopt;
  auto port = std::ranges::find(decl->ports, name, &PortDecl::name);
  if (port == decl->ports.end()) return std::nullopt;
  return DeclaredValue{OfLogicWhereImplicit(port->data_type),
                       static_cast<uint32_t>(port->unpacked_dims.size())};
}

static uint32_t UnpackedDimCount(const RtlirVariable& var) {
  if (var.num_unpacked_dims != 0) return var.num_unpacked_dims;
  bool is_array =
      var.unpacked_size != 0 || var.is_dynamic || var.is_queue || var.is_assoc;
  return is_array ? 1 : 0;
}

std::optional<DeclaredValue> NetOrVariableValue(const RtlirModule& mod,
                                                std::string_view declared) {
  auto net = std::ranges::find(mod.nets, declared, &RtlirNet::name);
  if (net != mod.nets.end()) {
    if (net->written_type == nullptr) return PortNetValue(declared, mod.decl);
    return DeclaredValue{OfLogicWhereImplicit(*net->written_type),
                         net->num_unpacked_dims};
  }
  auto var = std::ranges::find_if(mod.variables, [&](const RtlirVariable& v) {
    return v.name == declared && !v.is_enum_constant;
  });
  if (var != mod.variables.end()) {
    if (var->written_type == nullptr) return std::nullopt;
    return DeclaredValue{OfLogicWhereImplicit(*var->written_type),
                         UnpackedDimCount(*var)};
  }
  // A port the module records no net or variable for is kept as a port alone,
  // and is of the type its declaration writes. An interface port is of no data
  // type.
  auto port = std::ranges::find(mod.ports, declared, &RtlirPort::name);
  if (port == mod.ports.end() || port->is_interface_port) return std::nullopt;
  return PortNetValue(declared, mod.decl);
}

std::optional<DataType> NetOrVariableType(const RtlirModule& mod,
                                          std::string_view declared) {
  std::optional<DeclaredValue> value = NetOrVariableValue(mod, declared);
  if (!value || value->unpacked_dims != 0) return std::nullopt;
  return std::move(value->type);
}

}  // namespace delta
