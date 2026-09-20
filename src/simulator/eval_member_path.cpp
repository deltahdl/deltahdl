#include "simulator/eval_member_path.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "simulator/eval_expr_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

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

std::string TagKeyOfName(std::string_view name, SimContext& ctx) {
  if (ctx.FindLocalVariable(name) != nullptr) return std::string(name);
  std::string prefixed = ctx.ActiveInstancePrefix() + std::string(name);
  if (ctx.GetVariableStructType(prefixed) != nullptr) return prefixed;
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
