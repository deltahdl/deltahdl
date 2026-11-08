#include "simulator/eval_struct_property.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/struct_string_member.h"

namespace delta {

static bool IsTwoStateScalarKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return true;
    default:
      return false;
  }
}

static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

Logic4Vec ExtractStructField(const Logic4Vec& value, const StructTypeInfo* info,
                             std::string_view field, Arena& arena) {
  uint32_t bit_offset = 0;
  const StructFieldInfo* f = ResolveStructField(info, field, &bit_offset);
  if (f == nullptr) return MakeLogic4Vec(arena, 1);
  Logic4Vec slice = ExtractBitField(arena, value, bit_offset, f->width);
  if (f->type_kind == DataTypeKind::kString)
    return StringMemberText(slice, arena);
  if (IsTwoStateScalarKind(f->type_kind)) {
    for (uint32_t i = 0; i < slice.nwords; ++i) {
      slice.words[i].aval &= ~slice.words[i].bval;
      slice.words[i].bval = 0;
    }
  }
  slice.is_real = IsRealKind(f->type_kind);
  slice.is_signed = f->is_signed && !slice.is_real;
  return slice;
}

const StructFieldInfo* StructMemberOfClassType(const StructTypeInfo* info,
                                               std::string_view path,
                                               SimContext& ctx,
                                               uint32_t* bit_offset) {
  const StructFieldInfo* field = ResolveStructField(info, path, bit_offset);
  if (field == nullptr || ctx.FindClassType(field->type_name) == nullptr) {
    return nullptr;
  }
  return field;
}

std::optional<Logic4Vec> StructMemberObjectRead(const Logic4Vec& value,
                                                const StructTypeInfo* info,
                                                std::string_view field,
                                                SimContext& ctx, Arena& arena) {
  for (size_t dot = field.find('.'); dot != std::string_view::npos;
       dot = field.find('.', dot + 1)) {
    uint32_t bit_offset = 0;
    const StructFieldInfo* member =
        StructMemberOfClassType(info, field.substr(0, dot), ctx, &bit_offset);
    if (member == nullptr) continue;
    Logic4Vec handle = ExtractBitField(arena, value, bit_offset, member->width);
    ClassObject* obj = ctx.GetClassObject(handle.ToUint64());
    if (obj == nullptr) return std::nullopt;
    return ResolveClassFieldChain(obj, ctx.FindClassType(member->type_name),
                                  field.substr(dot + 1), ctx, arena);
  }
  return std::nullopt;
}

bool TryImplicitThisHandleMember(std::string_view base_name,
                                 std::string_view field_name, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  auto* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  Logic4Vec held = enclosing != nullptr
                       ? self->GetPropertyForType(base_name, enclosing, arena)
                       : self->GetProperty(base_name, arena);
  std::string path = std::string(base_name) + "." + std::string(field_name);
  PropertyFieldWindow window = ResolveClassPropertyField(
      enclosing != nullptr ? enclosing : self->type, path, ctx);
  if (window.valid) {
    out = MemberValueOf(
        ExtractBitField(arena, held, window.bit_offset, window.width),
        window.member_kind, arena);
    return true;
  }
  auto* obj = ctx.GetClassObject(held.ToUint64());
  if (obj == nullptr) return false;
  out = ResolveClassFieldChain(obj, nullptr, field_name, ctx, arena);
  return true;
}

}  // namespace delta
