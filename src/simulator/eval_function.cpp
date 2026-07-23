#include <algorithm>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/dpi.h"
#include "simulator/eval_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      ClassObject* obj, SimContext& ctx,
                                      Arena& arena) {
  for (const auto& prop : info->properties) {
    // §8.9: a static property is one shared copy that lives on the class type,
    // created and initialized once. Constructing an object must not give it a
    // private per-instance copy, or instance-qualified access would shadow the
    // shared storage. Leave static properties out of the instance map so reads
    // and writes fall through to the type's shared static_properties.
    if (prop.is_static) continue;
    // §8.7: a property is initialized to its explicit default if one is given,
    // otherwise to its type's uninitialized value — X for a 4-state type, 0 for
    // a 2-state one — rather than being forced to zero.
    Logic4Vec val;
    if (prop.init_expr) {
      val = EvalExpr(prop.init_expr, ctx, arena);
    } else if (prop.is_4state) {
      val = MakeAllX(arena, prop.width);
    } else {
      val = MakeLogic4VecVal(arena, prop.width, 0);
    }
    obj->properties[std::string(prop.name)] = val;
    std::string scoped =
        std::string(info->name) + "::" + std::string(prop.name);
    obj->properties[scoped] = val;
  }

  if (info->decl) {
    for (const auto& [pname, pexpr] : info->decl->params) {
      if (pexpr) {
        auto val = EvalExpr(pexpr, ctx, arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped =
            std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
  }
}

static void RunConstructorForLevel(const ClassTypeInfo* info, ClassObject*,
                                   const Expr* args_expr, SimContext& ctx,
                                   Arena& arena) {
  auto it = info->methods.find("new");
  if (it == info->methods.end() || !it->second) return;
  ctx.PushScope();
  // §8.15/§8.17: while this constructor body runs, `super` resolves relative to
  // `info` (the lexically enclosing class), not the dynamic type of the object.
  ctx.PushMethodClass(info);
  if (args_expr) BindFunctionArgs(it->second, args_expr, ctx, arena);
  Variable dummy;
  ExecFunctionBody(it->second, &dummy, ctx, arena);
  ctx.PopMethodClass();
  ctx.PopScope();
}

static size_t FindFirstDefaultArgPos(const ModuleItem* method) {
  for (size_t j = 0; j < method->func_args.size(); ++j) {
    if (method->func_args[j].is_default) {
      return j;
    }
  }
  return 0;
}

static size_t FindChildNewDefaultPos(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return FindFirstDefaultArgPos(m->method);
    }
  }
  return 0;
}

static const Expr* SynthDefaultExtendsArgs(const ClassTypeInfo* base,
                                           const ClassDecl* child_decl,
                                           const Expr* new_expr, Arena& arena) {
  size_t default_pos = FindChildNewDefaultPos(child_decl);

  size_t base_argc = 0;
  auto base_it = base->methods.find("new");
  if (base_it != base->methods.end() && base_it->second) {
    base_argc = base_it->second->func_args.size();
  }
  auto* synth = arena.Create<Expr>();
  synth->kind = ExprKind::kCall;
  for (size_t j = 0; j < base_argc && default_pos + j < new_expr->args.size();
       ++j) {
    synth->args.push_back(new_expr->args[default_pos + j]);
  }
  return synth;
}

// §8.17: whether the child class's own 'new' constructor argument list uses the
// 'default' keyword. When it does, the trailing actuals of the derived-most
// new() call expand to the superclass constructor's argument list.
static bool ChildNewUsesDefaultArg(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      for (const auto& a : m->method->func_args) {
        if (a.is_default) return true;
      }
      return false;
    }
  }
  return false;
}

static const Expr* ResolveConstructorArgsForLevel(
    const std::vector<const ClassTypeInfo*>& chain, size_t i,
    const Expr* new_expr, Arena& arena) {
  const Expr* args = (i == chain.size() - 1) ? new_expr : nullptr;
  if (args || i + 1 >= chain.size() || !chain[i + 1]->decl) return args;

  const auto* child_decl = chain[i + 1]->decl;
  if (!child_decl->extends_args.empty()) {
    auto* synth = arena.Create<Expr>();
    synth->kind = ExprKind::kCall;
    synth->args = child_decl->extends_args;
    return synth;
  }
  // §8.17: 'default' expands to the superclass constructor arguments, whether
  // it appears in the extends specifier (Base(default)) or in the subclass
  // constructor's own argument list (new(..., default)). Either way the
  // trailing actuals of the new() call are forwarded to this base level. This
  // also realizes the compiler-inserted super.new(default) when the subclass
  // body provides no explicit call.
  if ((child_decl->extends_has_default || ChildNewUsesDefaultArg(child_decl)) &&
      new_expr) {
    return SynthDefaultExtendsArgs(chain[i], child_decl, new_expr, arena);
  }
  return args;
}

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error({}, "cannot construct object of abstract class '" +
                                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error({}, "cannot construct object of interface class '" +
                                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;

  std::vector<const ClassTypeInfo*> chain;
  for (const auto* cur = info; cur; cur = cur->parent) chain.push_back(cur);
  std::reverse(chain.begin(), chain.end());

  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);

  for (size_t i = 0; i < chain.size(); ++i) {
    InitClassPropertyDefaults(chain[i], obj, ctx, arena);
    const Expr* args =
        ResolveConstructorArgsForLevel(chain, i, new_expr, arena);
    RunConstructorForLevel(chain[i], obj, args, ctx, arena);
  }

  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const auto& param_exprs = ctx.GetVariableClassParamExprs(var_name);
  if (param_exprs.empty()) return;
  const auto& params = obj->type->decl->params;
  for (size_t i = 0; i < params.size() && i < param_exprs.size(); ++i) {
    if (param_exprs[i]) {
      auto val = EvalExpr(param_exprs[i], ctx, arena);
      obj->properties[std::string(params[i].first)] = val;
      std::string scoped =
          std::string(obj->type->name) + "::" + std::string(params[i].first);
      obj->properties[scoped] = val;
    }
  }
}

// §35.6 / §11.13: binding context for resolving the actual arguments of a
// subroutine/let call. It bundles the call-site expression with the boundary
// between positional and named actuals (positional_count) and the evaluation
// environment, mirroring the single "call actuals" entity shared by DPI import
// and let-construct argument binding.
struct ActualBindingCtx {
  const Expr* call;
  size_t positional_count;
  SimContext& ctx;
  Arena& arena;
};

static int ResolveDpiActualIndex(const DpiFunction* import, const Expr* expr,
                                 size_t i, size_t positional_count) {
  if (i < positional_count) {
    return static_cast<int>(i);
  }
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == import->args[i].name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static uint64_t EvalDpiActualForFormal(const DpiFunction* import, size_t i,
                                       const ActualBindingCtx& b) {
  int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr) {
    return EvalExpr(b.call->args[static_cast<size_t>(ai)], b.ctx, b.arena)
        .ToUint64();
  }
  if (import->args[i].default_value) {
    return EvalExpr(import->args[i].default_value, b.ctx, b.arena).ToUint64();
  }
  return 0;
}

static std::vector<uint64_t> BindDpiActualsFromImport(const DpiFunction* import,
                                                      const Expr* expr,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  ActualBindingCtx binding{expr, positional_count, ctx, arena};
  std::vector<uint64_t> args;
  args.reserve(import->args.size());
  for (size_t i = 0; i < import->args.size(); ++i) {
    args.push_back(EvalDpiActualForFormal(import, i, binding));
  }
  return args;
}

static std::vector<uint64_t> BindDpiActualsPositional(const Expr* expr,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  std::vector<uint64_t> args;
  args.reserve(expr->args.size());
  for (auto* arg : expr->args) {
    args.push_back(EvalExpr(arg, ctx, arena).ToUint64());
  }
  return args;
}

static std::vector<uint64_t> BindDpiCallActuals(const DpiFunction* import,
                                                const Expr* expr,
                                                SimContext& ctx, Arena& arena) {
  if (import && !import->args.empty()) {
    return BindDpiActualsFromImport(import, expr, ctx, arena);
  }
  return BindDpiActualsPositional(expr, ctx, arena);
}

static Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiContext();
  if (!dpi || !dpi->HasImport(expr->callee)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §35.6: calling an imported function uses the same usage and syntax as a
  // native function call. When the import's formals are known, resolve the
  // call-site actuals against them so that named-argument binding and omitted
  // arguments backed by defaults behave exactly as for native subroutine calls.
  const DpiFunction* import = dpi->FindImport(expr->callee);
  std::vector<uint64_t> args = BindDpiCallActuals(import, expr, ctx, arena);
  uint64_t result = dpi->Call(expr->callee, args);
  return MakeLogic4VecVal(arena, 32, result);
}

// ClassMethodTarget and the ExecClassMethod prototype live in
// eval_function_internal.h (so eval_static_method.cpp can run a method body
// without a `this`); the definition is below.

struct InstanceMethodInfo {
  ClassObject* obj = nullptr;
  ModuleItem* method = nullptr;
  // The class in which `method` is defined, so its body resolves unqualified
  // members against that level (§8.15 member shadowing across a base/derived
  // hierarchy).
  const ClassTypeInfo* owner = nullptr;
};

static bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                                  InstanceMethodInfo& info) {
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return false;
  info.obj = ctx.GetClassObject(handle);
  if (!info.obj) return false;
  info.method = info.obj->ResolveVirtualMethod(parts.method_name, &info.owner);
  if (!info.method) {
    auto* declared_type = ctx.FindClassType(class_type);
    // §8.26.9: a non-interface declared type resolves against that type; an
    // interface-class declared type (or no declared type at all) resolves via
    // the object's dynamic type (the implementing class).
    const ClassTypeInfo* from = (declared_type && !declared_type->is_interface)
                                    ? declared_type
                                    : info.obj->type;
    info.method =
        info.obj->ResolveMethodForType(parts.method_name, from, &info.owner);
  }
  return info.method != nullptr;
}

Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  Logic4Vec out;
  ctx.PushScope();
  ctx.PushThis(obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ExecClassMethod({method}, expr, ctx, arena, out);
  WritebackOutputArgs(method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopThis();
  ctx.PopScope();
  return out;
}

static bool TryEvalSuperMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.var_name != "super") return false;
  // §8.17: super.new(default) forwards the constructor's default-expanded
  // arguments to the superclass. The flattened constructor chain already ran
  // the superclass constructor once with those forwarded actuals (see
  // ResolveConstructorArgsForLevel), so the explicit call here is satisfied
  // without a second base-constructor invocation -- which would otherwise bind
  // the literal 'default' token as an ordinary argument value.
  if (parts.method_name == "new" && expr->args.size() == 1 && expr->args[0] &&
      expr->args[0]->kind == ExprKind::kIdentifier &&
      expr->args[0]->text == "default") {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  auto* self = ctx.CurrentThis();
  if (!self || !self->type) return false;
  // §8.15: `super` refers to the parent of the lexically enclosing class. Using
  // the dynamic type of `this` here made super.new() in a mid-hierarchy
  // constructor resolve back to the same level and recurse forever.
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  const ClassTypeInfo* super_type =
      enclosing ? enclosing->parent : self->type->parent;
  if (!super_type) return false;
  const ClassTypeInfo* defining = nullptr;
  auto* method =
      self->ResolveMethodForType(parts.method_name, super_type, &defining);
  if (!method) return false;
  // Run the resolved method with its own defining class as the enclosing scope
  // so a nested super call walks one level further up, not back to here.
  ctx.PushMethodClass(defining);
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  // §8.10/§8.9: a static method invoked through an instance handle shares the
  // class's single static storage; dispatch it in class scope (no `this`).
  if (info.method->is_static) {
    RunStaticMethodInClassScope({info.method, info.obj->type}, expr, ctx, arena,
                                out);
    return true;
  }
  // Run the body with its defining class as the enclosing scope so an
  // unqualified member resolves to that level even when a derived class
  // shadows the name (§8.15).
  ctx.PushMethodClass(info.owner);
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  for (size_t i = 0; i < params.size(); ++i) {
    Logic4Vec val;
    if (i < values.size()) {
      val = EvalExpr(values[i], ctx, arena);
    } else if (params[i].second) {
      val = EvalExpr(params[i].second, ctx, arena);
    } else {
      val = MakeLogic4VecVal(arena, 32, 0);
    }
    auto* v = ctx.CreateLocalVariable(params[i].first, val.width);
    v->value = val;
    // §8.25.1: the same parameter is reachable inside the class -- and inside
    // its out-of-block methods, which resolve as though written in the class --
    // through the class scope resolution operator (`C::p`), which the evaluator
    // sees as a "Class.param" member reference. Bind that compound name to the
    // same value so `C::p` tracks the active specialization exactly as the bare
    // name `p` does, and is never shadowed by a same-named local variable.
    auto* qname = arena.Create<std::string>(std::string(cls->decl->name) + "." +
                                            std::string(params[i].first));
    auto* qv = ctx.CreateLocalVariable(*qname, val.width);
    qv->value = val;
  }
}

struct ClassScopeInfo {
  const Expr* access;
  ClassTypeInfo* cls;
  ModuleItem* method;
  bool is_void;
};

static bool ResolveClassScope(const Expr* expr, SimContext& ctx,
                              ClassScopeInfo& info) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  info.access = expr->lhs;
  if (!info.access->lhs || info.access->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!info.access->rhs || info.access->rhs->kind != ExprKind::kIdentifier)
    return false;
  info.cls = ctx.FindClassType(info.access->lhs->text);
  if (!info.cls) return false;
  auto it = info.cls->methods.find(std::string(info.access->rhs->text));
  if (it == info.cls->methods.end()) return false;
  info.method = it->second;
  info.is_void = (info.method->return_type.kind == DataTypeKind::kVoid);
  return true;
}

// Computes the width of a class method's return variable, evaluating the
// declared return type with the parameterized class's bound parameters in scope
// when available. Falls back to 32 bits when the width is indeterminate.
static uint32_t ComputeMethodReturnWidth(ModuleItem* method, SimContext& ctx,
                                         const ClassTypeInfo* param_cls) {
  if (param_cls && param_cls->decl) {
    ScopeMap scope;
    for (const auto& [pname, pexpr] : param_cls->decl->params) {
      auto* var = ctx.FindVariable(pname);
      if (var) scope[pname] = static_cast<int64_t>(var->value.ToUint64());
    }
    uint32_t width = EvalTypeWidth(method->return_type, {}, scope);
    return width == 0 ? 32 : width;
  }
  uint32_t width = EvalTypeWidth(method->return_type);
  return width == 0 ? 32 : width;
}

void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ModuleItem* method = target.method;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    ret_var = ctx.CreateLocalVariable(
        method->name, ComputeMethodReturnWidth(method, ctx, target.param_cls));
  }
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
}

static bool TryEvalClassScopeCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (!info.access->lhs->elements.empty()) return false;

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    return true;
  }
  ctx.PushScope();
  // §8.10: a static method can directly call static methods and access static
  // properties of the same class, so the class scope must be in effect while
  // the method body executes for unqualified same-class references to resolve.
  if (info.method->is_static) {
    ctx.PushMethodClass(info.cls);
  }
  ExecClassMethod({info.method}, expr, ctx, arena, out);
  // §13.5.2: output and inout arguments are copied back to the caller on
  // return. The instance-method path does this; the class-scope static path
  // must too, or `Cls::task(out_arg)` silently drops its results.
  WritebackOutputArgs(info.method, expr, ctx, arena);
  if (info.method->is_static) {
    ctx.PopMethodClass();
  }
  ctx.PopScope();
  return true;
}

static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (info.access->lhs->elements.empty()) return false;
  ctx.PushScope();
  BindClassParams(info.cls, info.access->lhs, ctx, arena);

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    ctx.PopScope();
    return true;
  }
  ExecClassMethod({info.method, info.cls}, expr, ctx, arena, out);
  // §13.5.2: copy output/inout arguments back to the caller on return (the
  // parameterized class-scope path, e.g. `Cls#(N)::task(out_arg)`).
  WritebackOutputArgs(info.method, expr, ctx, arena);
  ctx.PopScope();
  return true;
}

bool TryEvalTypedConstructorNew(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (!expr || expr->kind != ExprKind::kMemberAccess) return false;
  if (!expr->is_scope_resolution) return false;
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls) return false;
  // §8.25: a parameterized scope (E#(.N(77))::new) carries its specialization
  // overrides in the base identifier's elements; bind them as locals in a fresh
  // scope before constructing, mirroring the procedural assignment path.
  bool parameterized = !expr->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, expr->lhs, ctx, arena);
  }
  out = EvalClassNew(expr->lhs->text, nullptr, ctx, arena);
  if (parameterized) ctx.PopScope();
  return true;
}

static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "weak_reference")
    return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto wr_handle = var->value.ToUint64();
  auto* wr = ctx.FindWeakReferenceByHandle(wr_handle);
  if (parts.method_name == "get") {
    uint64_t referent = (wr != nullptr) ? wr->Get() : kNullClassHandle;
    out = MakeLogic4VecVal(arena, 64, referent);
    return true;
  }
  if (parts.method_name == "clear") {
    if (wr != nullptr) wr->Clear();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

static bool TryEvalWeakRefStaticCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "weak_reference") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "get_id") return false;
  if (expr->args.empty()) return false;
  uint64_t obj_handle = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  int64_t id = WeakReference::GetId(obj_handle);
  out = MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(id));
  return true;
}

static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalProcessMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEventTriggeredCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

static thread_local std::unordered_set<std::string_view> expanding_lets;

static int FindLetNamedActualIndex(const FunctionArg& formal, const Expr* call,
                                   size_t positional_count) {
  for (size_t j = 0; j < call->arg_names.size(); ++j) {
    if (call->arg_names[j] == formal.name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static Logic4Vec EvalLetActualForFormal(const FunctionArg& formal, size_t i,
                                        const ActualBindingCtx& b) {
  if (i < b.positional_count) {
    return EvalExpr(b.call->args[i], b.ctx, b.arena);
  }
  int found = FindLetNamedActualIndex(formal, b.call, b.positional_count);
  if (found >= 0 && b.call->args[static_cast<size_t>(found)]) {
    return EvalExpr(b.call->args[static_cast<size_t>(found)], b.ctx, b.arena);
  }
  if (formal.default_value) {
    return EvalExpr(formal.default_value, b.ctx, b.arena);
  }
  return MakeLogic4Vec(b.arena, 32);
}

// §11.12: the actual for a non-event typed formal is cast to the formal's type
// before substitution. A 2-state formal type (bit, byte, shortint, int,
// longint) cannot hold x/z, so the cast forces every unknown or high-impedance
// bit of the actual to 0 (example e spells this out: bits with an unknown logic
// value or a high-impedance value become 0).
static bool IsLetFormalTwoState(DataTypeKind kind) {
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

static Logic4Vec ResizeLetActualToFormal(Logic4Vec val,
                                         const FunctionArg& formal,
                                         Arena& arena) {
  const auto& dt = formal.data_type;
  if (dt.kind != DataTypeKind::kImplicit && dt.packed_dim_left &&
      dt.packed_dim_right) {
    uint32_t formal_width = EvalTypeWidth(dt);
    if (formal_width > 0 && formal_width != val.width) {
      val = ResizeToWidth(val, formal_width, arena);
    }
  }
  // §11.12 rule 2 / example e: casting to a 2-state typed formal drives every
  // unknown (x) or high-impedance (z) actual bit to 0. Work on a fresh copy so
  // the coercion never mutates a value shared with the actual's own storage.
  if (IsLetFormalTwoState(dt.kind)) {
    Logic4Vec coerced = ExtractBitField(arena, val, 0, val.width);
    coerced.is_signed = val.is_signed;
    for (uint32_t i = 0; i < coerced.nwords; ++i) {
      coerced.words[i].aval &= ~coerced.words[i].bval;
      coerced.words[i].bval = 0;
    }
    val = coerced;
  }
  return val;
}

static std::vector<Logic4Vec> EvalLetActuals(ModuleItem* decl, const Expr* call,
                                             SimContext& ctx, Arena& arena) {
  auto& formals = decl->func_args;
  size_t positional_count = call->args.size() - call->arg_names.size();
  ActualBindingCtx binding{call, positional_count, ctx, arena};
  std::vector<Logic4Vec> vals;
  vals.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val = EvalLetActualForFormal(formals[i], i, binding);
    val = ResizeLetActualToFormal(val, formals[i], arena);
    vals.push_back(val);
  }
  return vals;
}

static void BindLetArgs(ModuleItem* decl, const std::vector<Logic4Vec>& vals,
                        SimContext& ctx) {
  auto& formals = decl->func_args;
  for (size_t i = 0; i < formals.size(); ++i) {
    auto* var = ctx.CreateLocalVariable(formals[i].name, vals[i].width);
    var->value = vals[i];
  }
}

Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call, SimContext& ctx,
                           Arena& arena) {
  if (expanding_lets.count(decl->name)) {
    // §11.12: recursive let instantiations are not permitted. Report the
    // illegal self-reference rather than silently expanding it away, then
    // break the cycle by yielding x so the run can continue.
    ctx.GetDiag().Error(call ? call->range.start : SourceLoc{},
                        "recursive instantiation of let '" +
                            std::string(decl->name) +
                            "' is not permitted (§11.12)");
    return MakeAllX(arena, 32);
  }
  expanding_lets.insert(decl->name);

  auto vals = EvalLetActuals(decl, call, ctx, arena);

  auto saved_scopes = ctx.SwapScopeStack({});
  ctx.PushScope();
  BindLetArgs(decl, vals, ctx);
  auto result = EvalExpr(decl->init_expr, ctx, arena);
  ctx.PopScope();
  ctx.SwapScopeStack(std::move(saved_scopes));
  expanding_lets.erase(decl->name);
  return result;
}

static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalSuperMethodCall(expr, ctx, arena, out)) return true;
  // 18.6.3: randomize() is built-in and cannot be overridden, so a user class
  // never declares it; handle it before the user-method dispatch below.
  if (TryEvalRandomizeMethodCall(expr, ctx, arena, out)) return true;
  // 18.12: a scope randomize -- std::randomize(...) or the bare randomize(...)
  // spelling outside a class method -- randomizes the current scope's variables
  // rather than a class object's members. It has no receiver, so the class
  // randomize path above passes it over; handle it here before user dispatch.
  if (TryEvalScopeRandomizeCall(expr, ctx, arena, out)) return true;
  // §18.13.3: srandom() is a built-in method on any class handle and is never
  // user-declared, so seed the object's RNG before the user-method dispatch.
  if (TryEvalObjectSrandom(expr, ctx, arena, out)) return true;
  // §18.13.4/§18.13.5: get_randstate()/set_randstate() are built-in methods on
  // any class handle, never user-declared, so handle them before user dispatch.
  if (TryEvalObjectGetRandState(expr, ctx, arena, out)) return true;
  if (TryEvalObjectSetRandState(expr, ctx, arena, out)) return true;
  // §18.9: constraint_mode() is a built-in method on any class handle, never
  // user-declared, so handle it before the user-method dispatch below.
  if (TryEvalObjectConstraintMode(expr, ctx, arena, out)) return true;
  // §18.8: rand_mode() is likewise a built-in method on any class handle, never
  // user-declared, so handle it before the user-method dispatch below.
  if (TryEvalObjectRandMode(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  // §8.10: an unqualified call inside a static method resolves against the
  // enclosing class's static methods before module-level functions.
  if (TryEvalEnclosingStaticCall(expr, ctx, arena, out)) return true;
  auto* let_decl = ctx.FindLetDecl(expr->callee);
  if (let_decl) {
    out = EvalLetExpansion(let_decl, expr, ctx, arena);
    return true;
  }
  return false;
}

Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryDispatchMethodOrLet(expr, ctx, arena, result)) return result;

  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }

  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);

  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    uint32_t ret_width = EvalTypeWidth(func->return_type);
    if (ret_width == 0) ret_width = 32;
    ret_var =
        existing ? existing : ctx.CreateLocalVariable(func->name, ret_width);
  }

  // §20.17.2: a function body is a calling context on the $stacktrace chain,
  // so record its frame just as task calls do (see PushTaskCallScope).
  ctx.PushFuncName(func->name);
  // §21.2.1.5: a function is a subroutine level of the hierarchical name, so
  // %m inside its body names the function; task calls push the same scope in
  // ExecInlineTaskCall.
  ctx.PushActiveNamedScope(func->name);
  ctx.EnterFunction();
  ExecFunctionBody(func, ret_var, ctx, arena);
  ctx.ExitFunction();
  ctx.PopActiveNamedScope();
  ctx.PopFuncName();
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  result = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  return result;
}

static void PushTaskCallScope(const ModuleItem* func, SimContext& ctx) {
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ctx.PushFuncName(func->name);
}

static const ModuleItem* SetupTaskCallFromIdentifier(const Expr* expr,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  auto* func = ctx.FindFunction(expr->text);
  if (!func) return nullptr;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl;
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) return nullptr;

  PushTaskCallScope(func, ctx);
  if (is_void_func) ctx.EnterFunction();
  if (!func->func_args.empty()) BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;

  if (expr->kind == ExprKind::kIdentifier) {
    return SetupTaskCallFromIdentifier(expr, ctx, arena);
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  auto* func = ctx.FindFunction(expr->callee);
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;

  PushTaskCallScope(func, ctx);
  BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (is_void_func) ctx.ExitFunction();
  ctx.PopFuncName();
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
}

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  bool is_static = func->is_static && !func->is_automatic;
  if (!is_static) return;
  for (const auto& arg : func->func_args) {
    // §13.5.2: pass-by-reference is illegal in a static-lifetime subroutine,
    // except for a `ref static` argument, which is explicitly permitted.
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      diag.Error({}, "ref argument '" + std::string(arg.name) +
                         "' not allowed in static subroutine '" +
                         std::string(func->name) + "'");
    }
  }
}

static std::string_view GetLhsRootName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect && e->base) return GetLhsRootName(e->base);
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return GetLhsRootName(e->lhs);
  return {};
}

static void CheckConstRefWrites(
    const Stmt* stmt,
    const std::unordered_set<std::string_view>& const_ref_names,
    const ModuleItem* func, DiagEngine& diag) {
  if (!stmt) return;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kForce: {
      auto root = GetLhsRootName(stmt->lhs);
      if (!root.empty() && const_ref_names.count(root)) {
        diag.Error({}, "cannot write to const ref argument '" +
                           std::string(root) + "' in subroutine '" +
                           std::string(func->name) + "'");
      }
      break;
    }
    default:
      break;
  }
  for (auto* s : stmt->stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->then_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->else_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->body, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->for_body, const_ref_names, func, diag);
  for (auto* s : stmt->for_inits)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (auto* s : stmt->for_steps)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (const auto& ci : stmt->case_items)
    CheckConstRefWrites(ci.body, const_ref_names, func, diag);
  for (auto* s : stmt->fork_stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_pass_stmt, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_fail_stmt, const_ref_names, func, diag);
  for (const auto& ri : stmt->randcase_items)
    CheckConstRefWrites(ri.second, const_ref_names, func, diag);
}

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  std::unordered_set<std::string_view> const_ref_names;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef && arg.is_const) {
      const_ref_names.insert(arg.name);
    }
  }
  if (const_ref_names.empty()) return;
  for (auto* stmt : func->func_body_stmts) {
    CheckConstRefWrites(stmt, const_ref_names, func, diag);
  }
}

}  // namespace delta
