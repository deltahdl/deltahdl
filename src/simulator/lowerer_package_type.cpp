// The declared type of a package's or the compilation unit's data item, as
// the storage CreatePackageDataVariables makes for it reads it: the package's
// own typedef resolved under its "pk::name" key (WithPackageOwnType), and the
// kind a dump declares the variable by (RecordPackageVcdKind). Split out of
// lowerer_package_data.cpp, which reached the size the
// assert-no-oversized-source-files job fails at.

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

// §21.7.5 (Table 21-11) with §26.2: the declared type a dump declares a
// package's variable by, recorded as LowerVar records a module's
// (VcdEffectiveDeclKind in lowerer_var.cpp): a typedef name by the kind it
// stands for, a package's own under the "pk::name" key WithPackageOwnType
// scopes it to, an enumeration by the base type it writes -- or, through a
// typedef, as the integer its default int base makes it where its storage is
// int's 32 signed bits, and as a vector of its width otherwise -- and a packed
// structure as the bit vector it collapses to. Unrecorded, every package
// variable but a real was declared wire, the var_type of a net.
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

// §26.2 with §6.18: a package's variable written with a typedef the package
// itself declares, `ps_t pp` beside the package's `typedef ... ps_t`, has the
// type that typedef stands for, which the design's type tables hold under the
// "pk::ps_t" key. The declaration carries the bare name, and read by it the
// variable took none of the type's facts: a three-bit `pp` was given 32 bits
// and kept 127 from 7'h7f, a `byte` typedef lost its sign, and a `string`
// typedef was no string. Answers `item` where its type is no such name, and
// otherwise a copy whose type is scoped to the package, so that every fact
// read off the declaration by CreatePackageDataItem finds the typedef.
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
