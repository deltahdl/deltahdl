#include "simulator/eval_struct_property.h"

#include <cstdint>
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
#include "simulator/variable.h"

namespace delta {

// §7.3.1: a packed union with any 4-state member has 4-state storage, so a
// 2-state member aliases bits that may hold x/z. Reading such a member performs
// an implicit 4-state-to-2-state conversion (x/z become 0). For 2-state storage
// this is a no-op, so it is safe to apply to every 2-state member read.
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

// §6.12: a real, shortreal or realtime member holds a real, so the bits read
// from it are that real and not an integer of the same pattern.
static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

Logic4Vec ExtractStructField(Variable* base_var, const StructTypeInfo* info,
                             std::string_view field, Arena& arena) {
  uint32_t bit_offset = 0;
  const StructFieldInfo* f = ResolveStructField(info, field, &bit_offset);
  if (f == nullptr) return MakeLogic4Vec(arena, 1);
  Logic4Vec slice =
      ExtractBitField(arena, base_var->value, bit_offset, f->width);
  // §7.2 with §6.16: a string member's bits are a handle to its text.
  if (f->type_kind == DataTypeKind::kString)
    return StringMemberText(slice, arena);
  if (IsTwoStateScalarKind(f->type_kind)) {
    for (uint32_t i = 0; i < slice.nwords; ++i) {
      slice.words[i].aval &= ~slice.words[i].bval;
      slice.words[i].bval = 0;
    }
  }
  slice.is_real = IsRealKind(f->type_kind);
  // §7.2.1 with §6.11: a member reads as its own type, so `shortint address`
  // holding -2 is -2 and not 65534.
  slice.is_signed = f->is_signed && !slice.is_real;
  return slice;
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
  // §7.2 with §8.11: `p` declared with a structure's type holds that
  // structure, so `p.f` is the window of its value the member occupies, the
  // same window ResolveClassFieldTarget deposits `p.f = x` into. Asked before
  // the handle lookup, because a structure whose bits happen to equal a live
  // handle's number is still a structure. A member never written lies above
  // the top of the 32-bit carrier CollectClassMembers sized the property to,
  // which ExtractBitField reads as zero.
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
