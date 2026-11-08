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
  ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
    uint32_t width = EvalTypeWidth(EnumArrayElement(type), {});
    if (width == 0) width = 32;
    bool is_signed = IsSignedType(type, TypedefMap{});
    for (const auto& m : FoldEnumMembers(type.enum_members, values, arena)) {
      values[m.name] = m.value;
      auto* qname = arena.Create<std::string>(std::string(pkg_name) + "." +
                                              std::string(m.name));
      ctx.Vcd().MarkVcdEnumConstant(*qname);
      Variable* constant = ctx.CreateVariable(*qname, width);
      constant->value =
          MakeLogic4VecVal(arena, width, static_cast<uint64_t>(m.value));
      constant->is_signed = is_signed;
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
