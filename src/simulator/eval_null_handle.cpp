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
