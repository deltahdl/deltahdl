#include "simulator/eval_member_path.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "simulator/eval_expr_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// §23.6 with §8.5: the first dot of `h.p` parts the handle from the property,
// but a handle reached by a hierarchical path -- `i.c.v` for the class
// variable `c` an interface instance `i` declares -- has the instance path
// ahead of the handle's name, and the first dot puts `i`, which names no
// variable, on the handle side. Where the first segment names no variable, the
// split moves to the first dot after which the path so far names one, so the
// handle side is the instance-qualified variable and the property side what
// remains. A path no prefix of which names a variable keeps the first-dot
// split, and one with no dot answers npos.
size_t MemberPathSplit(const std::string& path, SimContext& ctx) {
  size_t first = path.find('.');
  if (first == std::string::npos) return first;
  std::string_view whole = path;
  if (ctx.FindVariable(whole.substr(0, first)) != nullptr) return first;
  for (size_t dot = path.find('.', first + 1); dot != std::string::npos;
       dot = path.find('.', dot + 1)) {
    if (ctx.FindVariable(whole.substr(0, dot)) != nullptr) return dot;
  }
  return first;
}

const StructTypeInfo* StructLayoutOfName(std::string_view name,
                                         SimContext& ctx) {
  if (ctx.FindLocalVariable(name) != nullptr) {
    return ctx.GetVariableStructType(name);
  }
  std::string prefixed = ctx.ActiveInstancePrefix() + std::string(name);
  if (const StructTypeInfo* info = ctx.GetVariableStructType(prefixed)) {
    return info;
  }
  return ctx.GetVariableStructType(name);
}

// §11.9 (printed page 304) with §3.12.1 (printed 56) and §26.3 (printed
// 810): a tagged union variable has one tag, whichever name it is written or
// read by, and the tag table (SimContext::var_tags_) keys it by name with no
// alias of its own, so an alias of a variable -- a module's bare `u` bound to
// the unit's "$unit.u" by AliasUnitDataItems, or an import's name bound to
// "pk.u" -- resolves to the key its storage stands under: the key its layout
// is registered by (StructTypeInfo::type_name, which the builder spells as
// the registration's key), where that key names the same variable as `key`
// does. A module's own declaration registers its layout under its storage
// key (RegisterAggregateLayout), so its key answers itself, and a package's
// or the unit's variable is given a registration under its own key when it
// is first aliased (AliasLayout in lowerer_alias_kinds.cpp); a name bound to
// a typedef's registration, which names no variable, keeps its key. Under
// the alias's own key, `u = tagged Other 3;` in a module declaring no u
// recorded Other under "u" while `$unit::u.Valid` read the initializer's
// Valid under "$unit.u" and passed a read the subclause reports.
static std::string StorageKeyOfLayout(const std::string& key, SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(key);
  if (info == nullptr || info->type_name == key) return key;
  Variable* own = ctx.FindVariable(key);
  if (own == nullptr || ctx.FindVariable(info->type_name) != own) return key;
  return std::string(info->type_name);
}

std::string TagKeyOfName(std::string_view name, SimContext& ctx) {
  if (ctx.FindLocalVariable(name) != nullptr) return std::string(name);
  std::string prefixed = ctx.ActiveInstancePrefix() + std::string(name);
  if (ctx.GetVariableStructType(prefixed) != nullptr)
    return StorageKeyOfLayout(prefixed, ctx);
  return std::string(name);
}

const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member) {
  for (const auto& field : sinfo.fields) {
    if (field.name == member && field.nested) return field.nested;
  }
  return nullptr;
}

}  // namespace delta
