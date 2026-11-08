#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

static const ClassTypeInfo* MethodDeclaringClass(const ModuleItem* method,
                                                 SimContext& ctx) {
  const ClassObject* self = ctx.CurrentThis();
  for (const ClassTypeInfo* t = self ? self->type : nullptr; t; t = t->parent) {
    for (const auto& [name, m] : t->methods) {
      if (m == method) return t;
    }
  }
  return nullptr;
}

static ScopeMap ClassConstantScope(const ClassTypeInfo* cls, SimContext& ctx) {
  ScopeMap scope;
  auto bind = [&](std::string_view pname) {
    auto held = cls->static_properties.find(std::string(pname));
    if (held != cls->static_properties.end()) {
      scope[pname] = static_cast<int64_t>(held->second.ToUint64());
    } else if (auto* var = ctx.FindVariable(pname)) {
      scope[pname] = static_cast<int64_t>(var->value.ToUint64());
    }
  };
  for (const auto& [pname, pexpr] : cls->decl->params) bind(pname);
  for (const auto* m : cls->decl->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param) bind(m->name);
  }
  return scope;
}

static uint32_t ComputeMethodReturnWidth(const ModuleItem* method,
                                         const DataType& type, SimContext& ctx,
                                         const ClassTypeInfo* param_cls) {
  if (param_cls == nullptr) param_cls = MethodDeclaringClass(method, ctx);
  if (param_cls && param_cls->decl) {
    ScopeMap scope = ClassConstantScope(param_cls, ctx);
    bool unfolded =
        type.packed_dim_left != nullptr && PackedDimProduct(type, scope) == 0;
    uint32_t width = unfolded ? 0 : EvalTypeWidth(type, {}, scope);
    if (width == 0 && !unfolded) width = ctx.FindTypeWidth(type.type_name);
    if (width != 0) return width;
  }
  uint32_t width = DeclaredTypeWidth(type, ctx);
  return width == 0 ? 32 : width;
}

Variable* CreateMethodReturnVariable(ClassMethodTarget target,
                                     SimContext& ctx) {
  const ModuleItem* method = target.method;
  const DataType& type =
      *TypeOfThisNamed(&method->return_type, ctx.CurrentMethodClass(), ctx);
  Variable* ret_var = ctx.CreateLocalVariable(
      method->name,
      ComputeMethodReturnWidth(method, type, ctx, target.param_cls),
      DeclaredTypeIsSigned(type, ctx));
  ret_var->is_4state = DeclaredTypeIs4State(type, ctx);
  ret_var->is_real = DeclaredTypeIsReal(type, ctx);
  return ret_var;
}

}  // namespace delta
