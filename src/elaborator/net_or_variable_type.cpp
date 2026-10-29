#include "elaborator/net_or_variable_type.h"

#include <algorithm>
#include <optional>
#include <string_view>

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

// §23.2.2.3: the type of the net the port `name` of `decl` declares.
static std::optional<DataType> PortNetType(std::string_view name,
                                           const ModuleDecl* decl) {
  if (decl == nullptr) return std::nullopt;
  auto port = std::ranges::find(decl->ports, name, &PortDecl::name);
  if (port == decl->ports.end() || !port->unpacked_dims.empty())
    return std::nullopt;
  return OfLogicWhereImplicit(port->data_type);
}

static bool HasUnpackedShape(const RtlirVariable& var) {
  return var.num_unpacked_dims != 0 || var.unpacked_size != 0 ||
         var.is_dynamic || var.is_queue || var.is_assoc;
}

std::optional<DataType> NetOrVariableType(const RtlirModule& mod,
                                          std::string_view declared) {
  auto net = std::ranges::find(mod.nets, declared, &RtlirNet::name);
  if (net != mod.nets.end()) {
    if (net->num_unpacked_dims != 0) return std::nullopt;
    if (net->written_type == nullptr) return PortNetType(declared, mod.decl);
    return OfLogicWhereImplicit(*net->written_type);
  }
  auto var = std::ranges::find_if(mod.variables, [&](const RtlirVariable& v) {
    return v.name == declared && !v.is_enum_constant;
  });
  if (var == mod.variables.end() || var->written_type == nullptr ||
      HasUnpackedShape(*var))
    return std::nullopt;
  return OfLogicWhereImplicit(*var->written_type);
}

}  // namespace delta
