#include "elaborator/net_or_variable_type.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/expression_self_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_expr.h"
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
  DeclaredValue value{OfLogicWhereImplicit(port->data_type),
                      static_cast<uint32_t>(port->unpacked_dims.size())};
  value.dims = port->unpacked_dims;
  return value;
}

// The unpacked dimensions `written` holds, where they are the `count` a value
// is recorded with, and none where they are not recorded or not all of them.
static std::vector<Expr*> RecordedDims(const std::vector<Expr*>* written,
                                       uint32_t count) {
  if (written == nullptr || written->size() != count) return {};
  return *written;
}

static uint32_t UnpackedDimCount(const RtlirVariable& var) {
  if (var.num_unpacked_dims != 0) return var.num_unpacked_dims;
  bool is_array =
      var.unpacked_size != 0 || var.is_dynamic || var.is_queue || var.is_assoc;
  return is_array ? 1 : 0;
}

static UnpackedKind OutermostKind(const RtlirVariable& var) {
  if (var.is_assoc) return UnpackedKind::kAssociative;
  if (var.is_queue) return UnpackedKind::kQueue;
  if (var.is_dynamic) return UnpackedKind::kDynamic;
  return UnpackedKind::kFixed;
}

static DataType NamedType(std::string_view name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = name;
  return named;
}

// §7.8: the index type the associative array `var` declares, as its
// declaration writes it (IndexDimType). Nothing for a wildcard index, which
// has no type.
static std::optional<DataType> AssociativeIndexType(const RtlirVariable& var) {
  if (!var.assoc_index_type_name.empty())
    return NamedType(var.assoc_index_type_name);
  if (!var.assoc_index_class_name.empty())
    return NamedType(var.assoc_index_class_name);
  if (var.declared_unpacked_dims == nullptr ||
      var.declared_unpacked_dims->empty()) {
    return std::nullopt;
  }
  return IndexDimType(var.declared_unpacked_dims->front());
}

std::optional<DeclaredValue> NetOrVariableValue(const RtlirModule& mod,
                                                std::string_view declared) {
  auto net = std::ranges::find(mod.nets, declared, &RtlirNet::name);
  if (net != mod.nets.end()) {
    if (net->written_type == nullptr) return PortNetValue(declared, mod.decl);
    DeclaredValue value{OfLogicWhereImplicit(*net->written_type),
                        net->num_unpacked_dims};
    value.dims =
        RecordedDims(net->declared_unpacked_dims, net->num_unpacked_dims);
    return value;
  }
  auto var = std::ranges::find_if(mod.variables, [&](const RtlirVariable& v) {
    return v.name == declared && !v.is_enum_constant;
  });
  if (var != mod.variables.end()) {
    if (var->written_type == nullptr) return std::nullopt;
    DeclaredValue value{OfLogicWhereImplicit(*var->written_type),
                        UnpackedDimCount(*var), OutermostKind(*var)};
    if (var->is_assoc) value.index_type = AssociativeIndexType(*var);
    value.dims = RecordedDims(var->declared_unpacked_dims, value.unpacked_dims);
    return value;
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
