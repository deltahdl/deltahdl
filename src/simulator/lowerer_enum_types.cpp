// §6.19 with §23.3: the enumerations a module declares, registered for the
// run as the module is lowered, and the enumeration a variable or a parameter
// is declared with, recorded beside it for §6.19.5's methods and casts.

#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "simulator/block_enums.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

void Lowerer::RegisterEnumForCast(std::string_view name,
                                  const RtlirVariable& var) {
  ctx_.SetVariableEnumType(name, var.enum_type_name);
}

// The width of the enumeration the module declares under `name`, and whether
// its base type is 4-state: a variable declared with it carries both, as the
// elaborator computed them from the declared type; the design's typedef
// table has the declaration of one no variable is declared with. The width
// is what BuildEnumMembers (src/elaborator/elaborator_typedef.cpp) gives
// each member's constant.
static void SetModuleEnumShape(const RtlirModule* mod,
                               const RtlirDesign* design, EnumTypeInfo& info) {
  for (const auto& v : mod->variables) {
    if (v.enum_type_name != info.type_name) continue;
    info.width = v.width;
    info.is_4state = v.is_4state;
    return;
  }
  if (design == nullptr) return;
  auto it = design->type_enums.find(info.type_name);
  if (it == design->type_enums.end() || it->second == nullptr) return;
  info.width = EvalTypeWidth(*it->second);
  info.is_4state = Is4stateType(*it->second, TypedefMap{});
}

void Lowerer::RegisterEnumTypes(const RtlirModule* mod) {
  for (const auto& [name, members] : mod->enum_types) {
    if (ctx_.FindEnumType(name)) continue;
    EnumTypeInfo info;
    info.type_name = name;
    SetModuleEnumShape(mod, design_, info);
    for (const auto& m : members) {
      info.members.push_back(EnumMemberInfoOf(m, info.width, ctx_, arena_));
    }
    ctx_.RegisterEnumType(name, info);
  }
  RegisterBlockEnumTypes(mod, design_, ctx_, arena_);
}

// A parameter is lowered to a variable ahead of the module's enumerations
// (Lowerer::LowerParams), so the enumeration its declared type names is
// looked up here, after them. A parameter declared with no type, or a type
// parameter, has no decl_type. The key is the one LowerParams stores the
// parameter under, a block's prefix included, arena-persisted as that one is
// because SimContext keys the table by string_view.
void Lowerer::RegisterParamEnumTypes(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    if (p.is_type_param || p.decl_type == nullptr) continue;
    auto* key = arena_.Create<std::string>(
        inst_prefix_ + std::string(p.gen_block_prefix) + std::string(p.name));
    RecordVariableEnumType(*key, *p.decl_type, ctx_);
  }
}

}  // namespace delta
