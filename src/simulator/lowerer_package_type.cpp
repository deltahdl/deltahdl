#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

void RecordPackageVcdKind(const ModuleItem* item, const Variable& var,
                          std::string_view qname, SimContext& ctx) {
  const DataType& type = item->data_type;
  DataTypeKind kind = DeclaredTypeKind(type, ctx);
  if (kind == DataTypeKind::kEnum &&
      type.enum_base_kind != DataTypeKind::kImplicit) {
    kind = type.enum_base_kind;
  } else if (kind == DataTypeKind::kEnum &&
             (var.value.width != 32 || !var.is_signed)) {
    kind = DataTypeKind::kBit;
  }
  const StructTypeInfo* st = ctx.GetVariableStructType(qname);
  if (kind == DataTypeKind::kStruct && st != nullptr && st->is_packed)
    kind = DataTypeKind::kBit;
  ctx.Vcd().SetVcdVarKind(qname, kind);
}

const ModuleItem* WithPackageOwnType(const ModuleItem* item,
                                     std::string_view pkg,
                                     const SimContext& ctx, Arena& arena) {
  const DataType& type = item->data_type;
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return item;
  std::string key = std::string(pkg) + "::" + std::string(type.type_name);
  if (ctx.FindTypeKind(key) == DataTypeKind::kNamed) return item;
  auto* scoped = arena.Create<ModuleItem>(*item);
  scoped->data_type.scope_name = pkg;
  return scoped;
}

}  // namespace delta
