// §6.19 with §26.3 (printed page 808 of IEEE 1800-2023): a
// package's enumeration constants given storage under their "pk.name" keys,
// and the folds of the package's parameters they are numbered over. Moved out
// of lowerer_register.cpp, which registers a module's own declarations, once
// the package's constants outgrew it.
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_class_params.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vcd_dump_state.h"

namespace delta {

std::optional<int64_t> FoldPackageParamValue(const ModuleItem& item,
                                             const PackageDecl& pkg,
                                             const ScopeMap& values,
                                             const SimContext& ctx) {
  DataType type = InPackageScope(item.data_type, pkg);
  return FoldParamValueAtWidth(item.init_expr, values,
                               SimParamTypeWidth(type, values, ctx),
                               SimParamTypeIsSigned(type, ctx));
}

// §6.19 makes an enumeration's members constants of the scope the enumeration
// is written in, and §26.3 references a package's declaration through the
// package scope resolution operator, so `pk::MED` names the package's constant
// from any scope, imported or not -- a class property's initializer, a write
// through a handle, a module's own expression. A wildcard import emits the
// literals as the importing module's variables (RegisterImportedEnumLiterals
// in elaborator_typedef.cpp) and a package parameter is created under its
// "pk.name" key (InitPackageDataVariables in lowerer.cpp), which is the key
// EvalMemberAccess reads a scoped name by; the package's enumeration constants
// alone had no storage, so `pk::MED` read 0 wherever it was written. Each is
// created under that key with its member's value, folded as the elaborator's
// RegisterPackageParams folds it: against the package's parameters and
// constants declared before it, which §6.20.1 and §6.19 let a member's value
// name, and at the width of the enumeration's base type.
static void RegisterPackageItemEnumConstants(const ModuleItem* item,
                                             const PackageDecl& pkg,
                                             ScopeMap& values, SimContext& ctx,
                                             Arena& arena) {
  std::string_view pkg_name = pkg.name;
  if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
    if (auto v = FoldPackageParamValue(*item, pkg, values, ctx))
      values[item->name] = *v;
    return;
  }
  // Syntax 6-5 lets the enumeration stand as the type a typedef names or as
  // the type of a data declaration, and §7.2 as the type of a member of a
  // structure or union either writes, which §23.9 makes no scope of its own;
  // the constants are the package's in each case, and each enumeration is
  // numbered on its own at the width of its own base type, which packed
  // dimensions after the body (§7.4.1) do not widen.
  ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
    uint32_t width = EvalTypeWidth(EnumArrayElement(type), {});
    if (width == 0) width = 32;
    for (const auto& m : FoldEnumMembers(type.enum_members, values, arena)) {
      values[m.name] = m.value;
      auto* qname = arena.Create<std::string>(std::string(pkg_name) + "." +
                                              std::string(m.name));
      ctx.Vcd().MarkVcdEnumConstant(*qname);
      ctx.CreateVariable(*qname, width)->value =
          MakeLogic4VecVal(arena, width, static_cast<uint64_t>(m.value));
    }
  });
}

void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena) {
  for (auto* pkg : design->packages) {
    ScopeMap values;
    for (auto* item : pkg->items)
      RegisterPackageItemEnumConstants(item, *pkg, values, ctx, arena);
  }
}

}  // namespace delta
