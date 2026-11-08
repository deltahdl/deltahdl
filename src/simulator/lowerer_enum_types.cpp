#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"
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

static uint32_t EnumWidthOfVariable(const RtlirVariable& v) {
  uint32_t elements = std::max<uint32_t>(
      1, EvalTypeWidth(*v.dtype) / EvalTypeWidth(EnumArrayElement(*v.dtype)));
  uint32_t width = v.width / elements;
  const DataType& written = *v.written_type;
  if (written.kind != DataTypeKind::kNamed ||
      written.packed_dim_left == nullptr) {
    return width;
  }
  return width / std::max<uint32_t>(1, PackedDimProduct(written));
}

static void SetModuleEnumShape(const RtlirModule* mod,
                               const RtlirDesign* design, EnumTypeInfo& info) {
  for (const auto& v : mod->variables) {
    if (v.enum_type_name != info.type_name) continue;
    info.width = EnumWidthOfVariable(v);
    info.is_4state = v.is_4state;
    info.is_signed = v.is_signed;
    return;
  }
  if (design == nullptr) return;
  auto it = design->type_enums.find(info.type_name);
  if (it == design->type_enums.end() || it->second == nullptr) return;
  info.width = EvalTypeWidth(EnumArrayElement(*it->second));
  info.is_4state = Is4stateType(*it->second, TypedefMap{});
  info.is_signed = IsSignedType(*it->second, TypedefMap{});
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

void Lowerer::RegisterParamEnumTypes(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    if (p.is_type_param || p.decl_type == nullptr) continue;
    auto* key = arena_.Create<std::string>(
        inst_prefix_ + std::string(p.gen_block_prefix) + std::string(p.name));
    RecordVariableEnumType(*key, *p.decl_type, ctx_);
  }
}

}  // namespace delta
