// §8.4 with §8.10: a call through a handle that refers to no object, named or
// held in an expression -- the static method it may still reach, and the
// report it otherwise draws. Split from eval_function.cpp, whose calls through
// a handle resolve here when the handle is null.

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.10 lets a static method be called through a handle referring to no
// object: the method is the declared class's, found up its base chain, and it
// runs in that class's scope with no object. §8.4 makes a non-static member
// or a virtual method accessed through a null handle illegal, the result
// indeterminate, and lets an implementation issue an error -- this one does,
// at the call, so that the 0 the call then yields is not read as a valid
// value. True where the static method was found and `info` names it.
bool ResolveStaticThroughNull(std::string_view method_name,
                              std::string_view class_type, SimContext& ctx,
                              InstanceMethodInfo& info) {
  const ClassTypeInfo* cls = ctx.FindClassType(class_type);
  if (cls == nullptr) return false;
  for (const auto* t = cls; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(method_name));
    if (it == t->methods.end()) continue;
    if (!it->second->is_static_method) return false;
    info.obj = nullptr;
    info.method = it->second;
    info.owner = t;
    return true;
  }
  return false;
}

void ReportNullHandleCall(std::string_view method_name, SourceLoc loc,
                          SimContext& ctx) {
  ctx.GetDiag().Error(
      loc,
      "method '" + std::string(method_name) + "' called through a null handle",
      Subclause("8.4"));
}

// The named-handle form of the rule above: a static method is found through
// the handle's declared class, and any other is reported naming the handle.
bool ResolveThroughNullHandle(const MethodCallParts& parts,
                              std::string_view class_type, SimContext& ctx,
                              InstanceMethodInfo& info) {
  if (ResolveStaticThroughNull(parts.method_name, class_type, ctx, info))
    return true;
  if (ctx.FindClassType(class_type) == nullptr) return false;
  if (!parts.loc.IsValid()) return false;
  ctx.GetDiag().Error(parts.loc,
                      "method '" + std::string(parts.method_name) +
                          "' called through the null handle '" +
                          std::string(parts.var_name) + "'",
                      Subclause("8.4"));
  return false;
}

}  // namespace delta
