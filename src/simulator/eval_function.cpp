#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static bool DeclarationIsVirtual(const ClassTypeInfo* defining,
                                 std::string_view name) {
  if (defining == nullptr || defining->decl == nullptr) return false;
  for (const auto* m : defining->decl->members) {
    if (m->kind != ClassMemberKind::kMethod || m->method == nullptr ||
        m->method->name != name) {
      continue;
    }
    return m->is_virtual || m->is_pure_virtual || m->method->is_method_extends;
  }
  return false;
}

static ModuleItem* ResolveNonVirtualFromDeclared(std::string_view method_name,
                                                 const ClassTypeInfo* declared,
                                                 InstanceMethodInfo& info) {
  if (declared == nullptr || declared->is_interface) return nullptr;
  if (declared->FindVTableIndex(method_name) >= 0) return nullptr;
  const ClassTypeInfo* defining = nullptr;
  ModuleItem* method =
      info.obj->ResolveMethodForType(method_name, declared, &defining);
  if (method == nullptr || DeclarationIsVirtual(defining, method_name))
    return nullptr;
  info.owner = defining;
  return method;
}

bool ResolveMethodByDeclaredClass(ClassObject* obj,
                                  std::string_view declared_class,
                                  std::string_view method_name, SimContext& ctx,
                                  InstanceMethodInfo& info) {
  info.obj = obj;
  if (obj == nullptr)
    return ResolveStaticThroughNull(method_name, declared_class, ctx, info);
  auto* declared_type = ctx.FindClassType(declared_class);
  info.method = ResolveNonVirtualFromDeclared(method_name, declared_type, info);
  if (!info.method)
    info.method = info.obj->ResolveVirtualMethod(method_name, &info.owner);
  if (!info.method) {
    const ClassTypeInfo* from = (declared_type && !declared_type->is_interface)
                                    ? declared_type
                                    : info.obj->type;
    info.method =
        info.obj->ResolveMethodForType(method_name, from, &info.owner);
  }
  return info.method != nullptr;
}

static bool ResolveMethodOnThis(std::string_view method_name, SimContext& ctx,
                                InstanceMethodInfo& info) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  info.obj = self;
  info.method = self->ResolveVirtualMethod(method_name, &info.owner);
  if (info.method == nullptr) {
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    info.method = self->ResolveMethodForType(
        method_name, enclosing != nullptr ? enclosing : self->type,
        &info.owner);
  }
  return info.method != nullptr;
}

static uint64_t HeldPropertyHandle(const ClassObject* self,
                                   const ClassTypeInfo* enclosing,
                                   std::string_view name) {
  const ClassTypeInfo* scope = enclosing != nullptr ? enclosing : self->type;
  const ClassTypeInfo* declarer =
      scope != nullptr ? scope->StaticPropertyDeclarer(name) : nullptr;
  if (declarer != nullptr)
    return declarer->static_properties.find(std::string(name))
        ->second.ToUint64();
  for (const auto* t = enclosing; t != nullptr; t = t->parent) {
    auto it =
        self->properties.find(std::string(t->name) + "::" + std::string(name));
    if (it != self->properties.end()) return it->second.ToUint64();
  }
  if (const Logic4Vec* held = self->FindPropertyValue(name))
    return held->ToUint64();
  return kNullClassHandle;
}

static bool ResolveMethodOnPropertyHandle(const MethodCallParts& parts,
                                          SimContext& ctx,
                                          InstanceMethodInfo& info) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr || NameDenotesVariable(parts.var_name, ctx)) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  std::string_view declared =
      PropertyClassName(self, enclosing, parts.var_name, ctx);
  if (declared.empty() || PropertyIsArray(enclosing, parts.var_name, ctx))
    return false;
  uint64_t handle = HeldPropertyHandle(self, enclosing, parts.var_name);
  if (handle == kNullClassHandle) {
    return ResolveThroughNullHandle(parts, declared, ctx, info);
  }
  return ResolveMethodByDeclaredClass(ctx.GetClassObject(handle), declared,
                                      parts.method_name, ctx, info);
}

static bool NameDenotesArrayOfHandles(std::string_view name, SimContext& ctx) {
  return ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr;
}

bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                           InstanceMethodInfo& info) {
  if (parts.var_name == "this")
    return ResolveMethodOnThis(parts.method_name, ctx, info);
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) {
    return ResolveMethodOnPropertyHandle(parts, ctx, info);
  }
  if (NameDenotesArrayOfHandles(parts.var_name, ctx)) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) {
    return ResolveThroughNullHandle(parts, class_type, ctx, info);
  }
  return ResolveMethodByDeclaredClass(ctx.GetClassObject(handle), class_type,
                                      parts.method_name, ctx, info);
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
  ctx.PopThis();
  WritebackOutputArgs(method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopScope();
  return out;
}

static bool TryEvalSuperMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.var_name != "super") return false;
  if (parts.method_name == "new" && IsSuperNewRunByConstruction(expr, ctx)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  auto* self = ctx.CurrentThis();
  if (!self || !self->type) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  const ClassTypeInfo* super_type =
      enclosing ? enclosing->parent : self->type->parent;
  if (!super_type) return false;
  const ClassTypeInfo* defining = nullptr;
  auto* method =
      self->ResolveMethodForType(parts.method_name, super_type, &defining);
  if (!method) return false;
  ctx.PushMethodClass(defining);
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

Logic4Vec RunInstanceMethod(const InstanceMethodInfo& info, const Expr* expr,
                            SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (info.method->is_static_method) {
    const ClassTypeInfo* scope =
        info.obj != nullptr ? info.obj->type : info.owner;
    RunStaticMethodInClassScope({info.method, scope}, expr, ctx, arena, out);
    return out;
  }
  ctx.PushMethodClass(info.owner);
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
  ctx.PopMethodClass();
  return out;
}

static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  ClassParamSizer sizer(cls->decl);
  sizer.UseTypeActuals(cls->param_actuals);
  for (size_t i = 0; i < params.size(); ++i) {
    if (cls->decl->param_port_unpacked_dims.count(params[i].first)) continue;
    Logic4Vec val;
    if (i < values.size()) {
      val = sizer.Value(i, values[i], ctx, arena);
    } else if (params[i].second) {
      val = sizer.Value(i, params[i].second, ctx, arena);
    } else {
      val = MakeLogic4VecVal(arena, 32, 0);
    }
    auto* v = ctx.CreateLocalVariable(params[i].first, val.width);
    v->value = val;
    auto* qname = arena.Create<std::string>(std::string(cls->decl->name) + "." +
                                            std::string(params[i].first));
    auto* qv = ctx.CreateLocalVariable(*qname, val.width);
    qv->value = val;
  }
}

struct ClassScopeInfo {
  const Expr* access;
  std::string_view class_name;
  ClassTypeInfo* cls;
  ModuleItem* method;
  bool is_void;
};

std::string_view ScopedClassKey(const Expr* scope, Arena& arena) {
  if (!scope) return {};
  if (scope->kind == ExprKind::kIdentifier) return scope->text;
  if (scope->kind != ExprKind::kMemberAccess || !scope->is_scope_resolution)
    return {};
  if (!scope->lhs || scope->lhs->kind != ExprKind::kIdentifier) return {};
  if (!scope->rhs || scope->rhs->kind != ExprKind::kIdentifier) return {};
  auto* key = arena.Create<std::string>(std::string(scope->lhs->text) +
                                        "::" + std::string(scope->rhs->text));
  return *key;
}

static bool FindInheritedMethod(std::string_view method_name, SimContext& ctx,
                                ClassScopeInfo& info) {
  std::string name(method_name);
  for (const ClassTypeInfo* t = info.cls; t != nullptr; t = t->parent) {
    auto it = t->methods.find(name);
    if (it == t->methods.end()) {
      if (name == "new") return false;
      continue;
    }
    info.method = it->second;
    if (info.method->is_static_method && t != info.cls) {
      if (ClassTypeInfo* declaring = ctx.FindClassType(t->name))
        info.cls = declaring;
    }
    return true;
  }
  return false;
}

static bool ResolveClassScope(const Expr* expr, SimContext& ctx, Arena& arena,
                              ClassScopeInfo& info) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  info.access = expr->lhs;
  info.class_name = ScopedClassKey(info.access->lhs, arena);
  if (info.class_name.empty()) return false;
  if (!info.access->rhs || info.access->rhs->kind != ExprKind::kIdentifier)
    return false;
  info.cls = ctx.FindClassType(info.class_name);
  if (!info.cls) info.cls = ClassNamedByTypeParam(info.class_name, ctx, arena);
  if (!info.cls) return false;
  if (!FindInheritedMethod(info.access->rhs->text, ctx, info)) return false;
  info.is_void = (info.method->return_type.kind == DataTypeKind::kVoid);
  return true;
}

static Logic4Vec CallResult(bool is_void, const Variable* ret_var,
                            Arena& arena) {
  if (is_void) return MakeLogic4VecVal(arena, 1, 0);
  Logic4Vec result = ret_var->value;
  result.is_string = ret_var->is_string;
  return result;
}

void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ModuleItem* method = target.method;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  ctx.EnterSubroutineScope(ctx.SubroutinePackage(method));
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) ret_var = CreateMethodReturnVariable(target, ctx);
  if (method->is_static_method) ctx.PushThis(nullptr);
  ExecFunctionBody(method, expr, ret_var, ctx, arena);
  if (method->is_static_method) ctx.PopThis();
  out = CallResult(is_void, ret_var, arena);
}

static bool TryEvalClassScopeCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, arena, info)) return false;
  if (!info.access->lhs->elements.empty()) return false;

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.class_name, expr, ctx, arena, expr->range.start);
    return true;
  }
  ctx.PushScope();
  if (info.method->is_static_method) {
    ctx.PushMethodClass(info.cls);
  }
  ExecClassMethod({info.method}, expr, ctx, arena, out);
  if (info.method->is_static_method) {
    ctx.PopMethodClass();
  }
  WritebackOutputArgs(info.method, expr, ctx, arena);
  ctx.PopScope();
  return true;
}

static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, arena, info)) return false;
  if (info.access->lhs->elements.empty()) return false;
  if (ClassTypeInfo* spec =
          ScopeNamedSpecialization(info.access->lhs, ctx, arena)) {
    info.cls = spec;
  }
  ctx.PushScope();
  BindClassParams(info.cls, info.access->lhs, ctx, arena);
  BindClassScopeTypeActuals(info.cls, info.access->lhs, ctx, arena);

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.class_name, expr, ctx, arena, expr->range.start);
    ctx.PopScope();
    return true;
  }
  if (info.method->is_static_method) ctx.PushMethodClass(info.cls);
  ExecClassMethod({info.method, info.cls}, expr, ctx, arena, out);
  if (info.method->is_static_method) ctx.PopMethodClass();
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
  bool parameterized = !expr->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, expr->lhs, ctx, arena);
  }
  out = EvalClassNew(expr->lhs->text, nullptr, ctx, arena, expr->range.start);
  if (parameterized) ctx.PopScope();
  return true;
}

static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
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
  if (TryEvalSemaphoreMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalMailboxMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalCovergroupMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEventTriggeredCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

static bool TryDispatchRandomizeMethod(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (TryEvalRandomizeMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalScopeRandomizeCall(expr, ctx, arena, out)) return true;
  if (TryEvalObjectSrandom(expr, ctx, arena, out)) return true;
  if (TryEvalObjectGetRandState(expr, ctx, arena, out)) return true;
  return TryEvalObjectSetRandState(expr, ctx, arena, out);
}

static bool TryDispatchModeMethod(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (TryEvalObjectConstraintMode(expr, ctx, arena, out)) return true;
  return TryEvalObjectRandMode(expr, ctx, arena, out);
}

static ModuleItem* FindCalledLet(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->callee.empty() && IsPackageScopedCall(expr))
    return ctx.FindLetDecl(ScopedClassKey(expr->lhs, arena));
  return FindVisibleLet(ctx, expr->callee);
}

static bool TryDispatchReceiverMethod(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  if (TryDispatchModeMethod(expr, ctx, arena, out)) return true;
  CallResultReceiverScope receiver(expr, ctx, arena);
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalSuperMethodCall(expr, ctx, arena, out)) return true;
  if (TryDispatchRandomizeMethod(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalCallResultMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalElementObjectMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalAssocElementMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalMethodOnEvaluatedBase(expr, ctx, arena, out);
}

static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryDispatchReceiverMethod(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnclosingStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnclosingInstanceCall(expr, ctx, arena, out)) return true;
  if (auto* let_decl = FindCalledLet(expr, ctx, arena)) {
    out = EvalLetExpansion(let_decl, expr, ctx, arena, CallContextWidth());
    return true;
  }
  return false;
}

static void RunFunctionBody(const SubroutineTarget& target, const Expr* call,
                            Variable* ret_var, SimContext& ctx, Arena& arena) {
  const ModuleItem* func = target.func;
  ctx.PushFuncName(func->name);
  ctx.PushActiveNamedScope(func->name);
  SampleAtBlockEvent(func->name, true, ctx, arena);
  ctx.EnterFunction();
  ExecFunctionBodyInCallee(target, call, ret_var, ctx, arena);
  ctx.ExitFunction();
  SampleAtBlockEvent(func->name, false, ctx, arena);
  ctx.PopActiveNamedScope();
  ctx.PopFuncName();
}

Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryDispatchMethodOrLet(expr, ctx, arena, result)) return result;

  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  EnterCalleeInstance(ctx, target);
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  ctx.EnterSubroutinePackage(func);
  BindGenBlockConsts(target, ctx, arena);

  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BindActualsInCaller(func, expr, ctx, arena);

  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    uint32_t ret_width = DeclaredTypeWidth(func->return_type, ctx);
    if (ret_width == 0) ret_width = 32;
    bool ret_signed = DeclaredTypeIsSigned(func->return_type, ctx);
    ret_var = existing
                  ? existing
                  : ctx.CreateLocalVariable(func->name, ret_width, ret_signed);
    ret_var->is_4state = DeclaredTypeIs4State(func->return_type, ctx);
    ret_var->is_real = DeclaredTypeIsReal(func->return_type, ctx);
  }

  RunFunctionBody(target, expr, ret_var, ctx, arena);
  WritebackInCaller(func, expr, ctx, arena);
  result = CallResult(is_void, ret_var, arena);

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  LeaveCalleeInstance(ctx);
  return result;
}

static void PushTaskCallScope(const SubroutineTarget& target, SimContext& ctx,
                              Arena& arena) {
  const ModuleItem* func = target.func;
  EnterCalleeInstance(ctx, target);
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  BindGenBlockConsts(target, ctx, arena);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ctx.PushFuncName(func->name);
}

static const ModuleItem* SetupTaskCallFromIdentifier(const Expr* expr,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func) return nullptr;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl;
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) return nullptr;

  PushTaskCallScope(target, ctx, arena);
  if (is_void_func) ctx.EnterFunction();
  if (!func->func_args.empty()) BindActualsInCaller(func, expr, ctx, arena);
  return func;
}

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;

  if (expr->kind == ExprKind::kIdentifier ||
      expr->kind == ExprKind::kMemberAccess) {
    return SetupTaskCallFromIdentifier(expr, ctx, arena);
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;

  PushTaskCallScope(target, ctx, arena);
  BindActualsInCaller(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  WritebackInCaller(func, expr, ctx, arena);
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
  LeaveCalleeInstance(ctx);
}

}  // namespace delta
