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

// The level of the running object's class chain that declares `method`, the
// class an instance method's constants are those of; null where none does.
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

// §8.25 and §6.20: the value parameters and localparams of the class `cls`
// by name, as the class or specialization holds them, or as the running frame
// binds one the class holds no value for.
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

// Computes the width of a class method's return variable, evaluating its
// declared return type `type` with the class's constants in scope
// (ClassConstantScope). The class is the one a static call names or, §13.4.1
// with §8.25, the level declaring an instance method, which was given none,
// so a range naming one folded to a single bit. Falls back to 32 bits when
// the width is indeterminate.
static uint32_t ComputeMethodReturnWidth(const ModuleItem* method,
                                         const DataType& type, SimContext& ctx,
                                         const ClassTypeInfo* param_cls) {
  if (param_cls == nullptr) param_cls = MethodDeclaringClass(method, ctx);
  if (param_cls && param_cls->decl) {
    ScopeMap scope = ClassConstantScope(param_cls, ctx);
    // A range the class's constants leave unfolded names something of the
    // running scope, a parameter of the module the class is declared in,
    // which DeclaredTypeWidth below reads; folded here it was one bit.
    bool unfolded =
        type.packed_dim_left != nullptr && PackedDimProduct(type, scope) == 0;
    uint32_t width = unfolded ? 0 : EvalTypeWidth(type, {}, scope);
    // Not DeclaredTypeWidth here: that asks the one-argument EvalTypeWidth,
    // which would drop the bound parameters `scope` carries and so mis-size a
    // return type whose dimensions name one. Resolve a typedef name against the
    // same table DeclaredTypeWidth uses, but only once the scope-aware overload
    // has had its say.
    if (width == 0 && !unfolded) width = ctx.FindTypeWidth(type.type_name);
    if (width != 0) return width;
  }
  uint32_t width = DeclaredTypeWidth(type, ctx);
  return width == 0 ? 32 : width;
}

Variable* CreateMethodReturnVariable(ClassMethodTarget target,
                                     SimContext& ctx) {
  const ModuleItem* method = target.method;
  // §6.23 with §8.11: a method declared to return type(this) returns a handle
  // of the class it runs in, as one declared to return that class by name
  // does; read as written, the type was implicit and the variable one bit,
  // which kept the low bit of the handle the body returned.
  const DataType& type =
      *TypeOfThisNamed(&method->return_type, ctx.CurrentMethodClass(), ctx);
  // §6.11.3: a method's return type decides the signedness of the variable
  // that holds its result, exactly as a plain function's does in
  // EvalFunctionCall.
  Variable* ret_var = ctx.CreateLocalVariable(
      method->name,
      ComputeMethodReturnWidth(method, type, ctx, target.param_cls),
      DeclaredTypeIsSigned(type, ctx));
  // §13.4.1 gives the implicit variable the method's return type, so §6.11.2
  // decides whether it holds unknowns as it does for any other object.
  ret_var->is_4state = DeclaredTypeIs4State(type, ctx);
  // §13.4.1 with §6.12: a method returning real holds its result in a real
  // variable, as EvalFunctionCall's does; a `return i` of an integer then
  // converts under §6.12.1 (ExecFuncReturn) rather than handing out the
  // integer's bits as a double.
  ret_var->is_real = DeclaredTypeIsReal(type, ctx);
  return ret_var;
}

}  // namespace delta
