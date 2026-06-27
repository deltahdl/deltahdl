#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.10: run a static method with its class in scope but no `this`. Class scope
// makes unqualified references to the class's static methods/properties resolve
// to the single shared copy (see EvalIdentifier / ExecFuncIdentifierAssign).
// target.param_cls doubles as the scope class (as for the parameterized
// class-scope path), so a parameterized static method's return width resolves.
void RunStaticMethodInClassScope(ClassMethodTarget target, const Expr* expr,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec& out) {
  ctx.PushScope();
  ctx.PushMethodClass(target.param_cls);
  ExecClassMethod(target, expr, ctx, arena, out);
  // §13.5.2: copy output/inout arguments back to the caller on return.
  WritebackOutputArgs(target.method, expr, ctx, arena);
  ctx.PopMethodClass();
  ctx.PopScope();
}

bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (!cls) return false;
  auto it = cls->methods.find(std::string(expr->callee));
  if (it == cls->methods.end() || !it->second->is_static) return false;
  RunStaticMethodInClassScope({it->second, cls}, expr, ctx, arena, out);
  return true;
}

}  // namespace delta
