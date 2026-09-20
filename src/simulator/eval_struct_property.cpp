#include "simulator/eval_struct_property.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/class_object.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

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
    out = ExtractBitField(arena, held, window.bit_offset, window.width);
    return true;
  }
  auto* obj = ctx.GetClassObject(held.ToUint64());
  if (obj == nullptr) return false;
  out = ResolveClassFieldChain(obj, nullptr, field_name, ctx, arena);
  return true;
}

}  // namespace delta
