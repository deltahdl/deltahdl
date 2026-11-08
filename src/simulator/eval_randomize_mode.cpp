#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

bool ExtractConstraintModeParts(const Expr* expr, std::string_view& obj_name,
                                std::string_view& constraint_name) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "constraint_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    constraint_name = {};
    return true;
  }
  if (recv->kind == ExprKind::kMemberAccess && !recv->is_scope_resolution &&
      recv->lhs && recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    constraint_name = recv->rhs->text;
    return true;
  }
  return false;
}

static const Expr* VariablePathRoot(const Expr* recv) {
  const Expr* e = recv;
  while (e->kind == ExprKind::kSelect ||
         (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
          e->lhs->kind != ExprKind::kIdentifier)) {
    e = e->kind == ExprKind::kSelect ? e->base : e->lhs;
  }
  if (e == recv || e->kind != ExprKind::kMemberAccess ||
      e->is_scope_resolution) {
    return nullptr;
  }
  return e;
}

static std::string VariablePathKey(const Expr* path, const Expr* root,
                                   std::string_view name, SimContext& ctx,
                                   Arena& arena) {
  if (path == root) return std::string(name);
  if (path->kind == ExprKind::kSelect) {
    auto index =
        static_cast<int64_t>(EvalExpr(path->index, ctx, arena).ToUint64());
    return ClassArrayElementKey(
        VariablePathKey(path->base, root, name, ctx, arena), index);
  }
  return VariablePathKey(path->lhs, root, name, ctx, arena) + "." +
         std::string(path->rhs->text);
}

bool ExtractRandModeParts(const Expr* expr, std::string_view& obj_name,
                          std::string_view& var_name, const Expr*& element) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "rand_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  element = nullptr;
  if (const Expr* root = VariablePathRoot(recv)) {
    obj_name = root->lhs->text;
    var_name = root->rhs->text;
    element = recv;
    return true;
  }
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    var_name = {};
    return true;
  }
  if (recv->kind == ExprKind::kMemberAccess && !recv->is_scope_resolution &&
      recv->lhs && recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    var_name = recv->rhs->text;
    return true;
  }
  return false;
}

struct ScopedModeParts {
  std::string_view obj_name;
  std::string_view name;
  const Expr* element = nullptr;
};

static bool ExtractScopedModeParts(const Expr* expr, std::string_view method,
                                   Arena& arena, ScopedModeParts& out) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess || !callee->rhs ||
      callee->rhs->kind != ExprKind::kIdentifier ||
      callee->rhs->text != method || !callee->lhs) {
    return false;
  }
  const Expr* recv = callee->lhs;
  out.element = nullptr;
  MethodCallParts parts;
  if (recv->kind == ExprKind::kMemberAccess && recv->is_scope_resolution) {
    if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
    out.obj_name = parts.var_name;
    out.name = {};
    return true;
  }
  if (method == "rand_mode" && recv->kind == ExprKind::kSelect &&
      recv->index != nullptr && recv->index_end == nullptr &&
      recv->base != nullptr) {
    out.element = recv;
    recv = recv->base;
  }
  if (recv->kind != ExprKind::kMemberAccess || !recv->lhs ||
      recv->lhs->kind != ExprKind::kMemberAccess ||
      !recv->lhs->is_scope_resolution ||
      !ExtractHandleAccessParts(recv, arena, parts)) {
    return false;
  }
  out.obj_name = parts.var_name;
  out.name = parts.method_name;
  return true;
}

const ClassTypeInfo* StaticRandOwner(const ClassObject* obj,
                                     std::string_view name) {
  std::string_view base = name.substr(0, name.find_first_of("[."));
  for (const auto* t = obj->type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == base)
        return m->is_static ? t : nullptr;
    }
  }
  return nullptr;
}

bool IsObjectRandActive(const ClassObject* obj, std::string_view name) {
  const ClassTypeInfo* owner = StaticRandOwner(obj, name);
  const auto& modes =
      owner != nullptr ? owner->static_rand_active : obj->rand_active;
  std::string key(name);
  for (;;) {
    auto it = modes.find(key);
    if (it != modes.end()) return it->second;
    auto cut = key.find_last_of("[.");
    if (cut == std::string::npos) return true;
    key.resize(cut);
  }
}

void InvokePostRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                         Arena& arena) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* post =
          obj->ResolveMethodForType("post_randomize", obj->type, &owner)) {
    ctx.PushMethodClass(owner);
    ExecInstanceMethodCall(post, obj, expr, ctx, arena);
    ctx.PopMethodClass();
  }
}

void CollectRandObjectMembers(const ClassTypeInfo* type, SimContext& ctx,
                              std::vector<std::string>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && IsClassHandleMember(m, ctx))
        out.push_back(std::string(m->name));
    }
  }
}

struct InlineRandomArgs {
  std::unordered_set<std::string> names;
  bool has_list;
  bool null_checker;
};

InlineRandomArgs CollectInlineRandomArgs(const Expr* expr) {
  InlineRandomArgs args{{}, false, false};
  for (const Expr* arg : expr->args) {
    if (arg != nullptr && arg->kind == ExprKind::kIdentifier &&
        arg->text == "null") {
      args.names.clear();
      args.has_list = false;
      args.null_checker = true;
      return args;
    }
    std::string_view nm = InlineRandomArgName(arg);
    if (!nm.empty()) {
      args.names.insert(std::string(nm));
      args.has_list = true;
    }
  }
  return args;
}

static bool RandomizeCall(const Expr* expr, ClassObject* obj,
                          const InlineRandomArgs& args, SimContext& ctx,
                          Arena& arena) {
  std::vector<JointObject> objects;
  if (args.null_checker) {
    InvokePreRandomize(obj, expr, ctx, arena);
    objects.push_back({obj, ""});
  } else {
    objects = CollectActiveRandomObjects(obj, expr, ctx, arena);
  }
  if (!args.null_checker && !args.has_list && !expr->with_has_parens &&
      objects.size() > 1) {
    return RandomizeObjectTree(ctx, arena, expr, objects,
                               expr->inline_constraint);
  }
  const std::unordered_set<std::string>* active_set =
      (args.null_checker || args.has_list) ? &args.names : nullptr;
  return RandomizeEachObject(
      objects, {expr, expr->inline_constraint, active_set, args.null_checker},
      ctx, arena);
}

namespace {

bool BareRandomizeInMethod(const Expr* expr, SimContext& ctx,
                           MethodCallParts& parts) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier ||
      expr->lhs->text != "randomize" || ctx.CurrentThis() == nullptr)
    return false;
  parts.var_name = "this";
  parts.method_name = "randomize";
  return true;
}

const Expr* ReceiverOfMethod(const Expr* expr, std::string_view method) {
  if (expr->kind != ExprKind::kCall) return nullptr;
  const Expr* callee = expr->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->is_scope_resolution || callee->lhs == nullptr ||
      callee->rhs == nullptr || callee->rhs->kind != ExprKind::kIdentifier ||
      callee->rhs->text != method) {
    return nullptr;
  }
  return callee->lhs;
}

ClassObject* ExprReceiverObject(const Expr* expr, std::string_view method,
                                SimContext& ctx, Arena& arena) {
  const Expr* recv = ReceiverOfMethod(expr, method);
  if (recv == nullptr) return nullptr;
  uint64_t handle = EvalExpr(recv, ctx, arena).ToUint64();
  if (handle == kNullClassHandle) {
    ReportNullHandleCall(method, expr->lhs->rhs->range.start, ctx);
    return nullptr;
  }
  ClassObject* obj = ctx.GetClassObject(handle);
  return (obj != nullptr && obj->type != nullptr) ? obj : nullptr;
}

ClassObject* ObjectMethodReceiver(const Expr* expr, std::string_view method,
                                  SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (ExtractHandleMethodCallParts(expr, arena, parts)) {
    return parts.method_name == method ? ResolveRandomizeTarget(ctx, parts)
                                       : nullptr;
  }
  return ExprReceiverObject(expr, method, ctx, arena);
}

}  // namespace

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  ClassObject* obj = BareRandomizeInMethod(expr, ctx, parts)
                         ? ResolveRandomizeTarget(ctx, parts)
                         : ObjectMethodReceiver(expr, "randomize", ctx, arena);
  if (!obj) return false;

  InlineRandomArgs args = CollectInlineRandomArgs(expr);
  ctx.PushScope();
  BindLocalQualifiedNames(expr, ctx, arena);
  BindCallersMembers(expr, obj, ctx, arena);
  BindCallersVariables(expr, obj, ctx, arena);
  BindObjectHandleHeads(expr, obj, ctx, arena);
  bool solved = RandomizeCall(expr, obj, args, ctx, arena);
  ctx.PopScope();
  out = MakeLogic4VecVal(arena, 32, solved ? 1 : 0);
  return true;
}

namespace {

bool IsScopeRandomizeForm(const Expr* expr, SimContext& ctx) {
  if (expr == nullptr || expr->kind != ExprKind::kCall || expr->lhs == nullptr)
    return false;
  const Expr* callee = expr->lhs;
  if (callee->kind == ExprKind::kMemberAccess && callee->rhs != nullptr &&
      callee->rhs->kind == ExprKind::kIdentifier &&
      callee->rhs->text == "randomize" && callee->lhs != nullptr &&
      callee->lhs->kind == ExprKind::kIdentifier && callee->lhs->text == "std")
    return true;
  if (callee->kind == ExprKind::kIdentifier && callee->text == "randomize" &&
      ctx.CurrentMethodClass() == nullptr && ctx.CurrentThis() == nullptr)
    return true;
  return false;
}

uint64_t ScopeConstraintsHold(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->inline_constraint == nullptr) return 1;
  for (const Expr* rel : expr->inline_constraint->constraint_exprs) {
    if (EvalExpr(rel, ctx, arena).ToUint64() == 0) return 0;
  }
  return 1;
}

}  // namespace

std::vector<RandInfo> MakeScopeRandVariables(
    const std::vector<Variable*>& targets,
    const std::vector<std::string>& names) {
  std::vector<RandInfo> rands;
  rands.reserve(targets.size());
  for (size_t i = 0; i < targets.size(); ++i) {
    uint32_t w = targets[i]->value.width;
    if (w == 0) w = 32;
    RandInfo ri;
    ri.name = names[i];
    ri.var.name = names[i];
    ri.var.width = w;
    ri.var.is_signed = targets[i]->is_signed;
    ri.var.BindDomainToDeclaredRange();
    ri.var.value = ri.var.ValueFromBits(targets[i]->value.ToUint64());
    rands.push_back(std::move(ri));
  }
  return rands;
}

std::vector<ConstraintExpr> TranslateScopeWithBlock(
    const Expr* expr, std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  std::vector<ConstraintExpr> with_constraints;
  if (expr->inline_constraint == nullptr) return with_constraints;
  with_constraints.reserve(expr->inline_constraint->constraint_exprs.size());
  for (const Expr* rel : expr->inline_constraint->constraint_exprs)
    with_constraints.push_back(TranslateRelation(rel, rands, rc));
  return with_constraints;
}

void WriteBackScopeSolved(const std::vector<Variable*>& targets,
                          const std::vector<std::string>& names,
                          const ConstraintSolver& solver, Arena& arena) {
  for (size_t i = 0; i < targets.size(); ++i) {
    uint32_t w = targets[i]->value.width;
    if (w == 0) w = 32;
    targets[i]->value = MakeLogic4VecVal(
        arena, w, static_cast<uint64_t>(solver.GetValue(names[i])));
  }
}

struct ScopeTargets {
  std::vector<Variable*> vars;
  std::vector<std::string> names;
  std::vector<std::pair<Variable*, FieldTarget>> properties;
};

static bool ResolveScopeTargets(const Expr* expr, SimContext& ctx, Arena& arena,
                                ScopeTargets& out) {
  for (const Expr* arg : expr->args) {
    if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
    Variable* var = ctx.FindVariable(arg->text);
    if (var == nullptr) {
      FieldTarget field = ResolveBarePropertyTarget(arg->text, ctx);
      if (!field.HasDeposit()) return false;
      var = arena.Create<Variable>();
      var->value = EvalExpr(arg, ctx, arena);
      var->is_signed = var->value.is_signed;
      out.properties.emplace_back(var, field);
    }
    out.vars.push_back(var);
    out.names.emplace_back(arg->text);
  }
  return true;
}

bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (!IsScopeRandomizeForm(expr, ctx)) return false;

  ScopeTargets scope;
  if (!ResolveScopeTargets(expr, ctx, arena, scope)) return false;
  std::vector<Variable*>& targets = scope.vars;
  std::vector<std::string>& names = scope.names;

  if (targets.empty()) {
    out = MakeLogic4VecVal(arena, 32, ScopeConstraintsHold(expr, ctx, arena));
    return true;
  }

  ConstraintSolver solver(static_cast<uint32_t>(ctx.ActiveRng()()));
  std::vector<RandInfo> rands = MakeScopeRandVariables(targets, names);

  RandomizeCtx rc{nullptr, ctx, arena};
  rc.solver = &solver;
  std::vector<ConstraintExpr> with_constraints =
      TranslateScopeWithBlock(expr, rands, rc);

  for (auto& ri : rands) {
    ri.var.CollapseEmptyDomain();
    solver.AddVariable(ri.var);
  }

  bool ok = solver.SolveWith(with_constraints);

  if (ok) {
    WriteBackScopeSolved(targets, names, solver, arena);
    for (const auto& [stand_in, field] : scope.properties)
      WriteResolvedField(field, stand_in->value, ctx, arena);
  }
  out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
  return true;
}

bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out) {
  ClassObject* obj = ObjectMethodReceiver(expr, "srandom", ctx, arena);
  if (!obj) return false;

  uint32_t seed = 0;
  if (!expr->args.empty()) {
    seed =
        static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  }
  ctx.SeedObjectRng(obj, seed);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectGetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  ClassObject* obj = ObjectMethodReceiver(expr, "get_randstate", ctx, arena);
  if (!obj) return false;

  out = StringToLogic4Vec(arena, ctx.GetRandState(obj));
  out.is_string = true;
  return true;
}

bool TryEvalObjectSetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  ClassObject* obj = ObjectMethodReceiver(expr, "set_randstate", ctx, arena);
  if (!obj) return false;

  std::string state;
  if (!expr->args.empty()) {
    state = Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
  }
  ctx.SetRandState(obj, state);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

void SetAllConstraintsActive(ClassObject* obj, bool on) {
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint)
        SetObjectConstraintActive(obj, m->name, on);
    }
  }
}

void SetAllRandVariablesActive(ClassObject* obj, bool on) {
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && (m->is_rand || m->is_randc))
        SetObjectRandActive(obj, m->name, on);
    }
  }
}

namespace {

struct ModeTarget {
  ClassObject* obj = nullptr;
  std::string_view name;
  const Expr* element = nullptr;
};

bool DeclaresModeMemberIn(const ClassDecl* decl, std::string_view name,
                          bool block) {
  for (const ClassMember* m : decl->members) {
    if (m->name != name) continue;
    if (block ? m->kind == ClassMemberKind::kConstraint
              : m->kind == ClassMemberKind::kProperty &&
                    (m->is_rand || m->is_randc)) {
      return true;
    }
  }
  return false;
}

bool DeclaresModeMember(const ClassObject* obj, std::string_view name,
                        std::string_view method) {
  bool block = method == "constraint_mode";
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl != nullptr && DeclaresModeMemberIn(lvl->decl, name, block))
      return true;
  }
  return false;
}

ClassObject* ModeObject(const Logic4Vec& value, const Expr* call,
                        SimContext& ctx) {
  uint64_t handle = value.ToUint64();
  if (handle == kNullClassHandle) {
    ReportNullHandleCall(call->lhs->rhs->text, call->lhs->rhs->range.start,
                         ctx);
  }
  return ctx.GetClassObject(handle);
}

bool ResolveExprModeTarget(const Expr* expr, std::string_view method,
                           SimContext& ctx, Arena& arena, ModeTarget& out) {
  const Expr* recv = ReceiverOfMethod(expr, method);
  if (recv == nullptr) return false;
  const Expr* member = recv;
  if (method == "rand_mode" && recv->kind == ExprKind::kSelect &&
      recv->index != nullptr && recv->index_end == nullptr &&
      recv->base != nullptr) {
    member = recv->base;
  }
  if (member->kind != ExprKind::kMemberAccess || member->is_scope_resolution ||
      member->lhs == nullptr || member->rhs == nullptr ||
      member->rhs->kind != ExprKind::kIdentifier) {
    out.obj = ModeObject(EvalExpr(recv, ctx, arena), expr, ctx);
    return true;
  }
  Logic4Vec owner_value = EvalExpr(member->lhs, ctx, arena);
  ClassObject* owner = ModeObject(owner_value, expr, ctx);
  if (owner == nullptr) return true;
  if (DeclaresModeMember(owner, member->rhs->text, method)) {
    out = {owner, member->rhs->text, member == recv ? nullptr : recv};
    return true;
  }
  ctx.SetDeferredArgSnapshot(member->lhs, owner_value);
  out.obj = ModeObject(EvalExpr(recv, ctx, arena), expr, ctx);
  ctx.ClearDeferredArgSnapshot(member->lhs);
  return true;
}

bool PathThroughHandle(const ModeTarget& t, SimContext& ctx) {
  bool member = false;
  for (const Expr* e = t.element; e->kind != ExprKind::kMemberAccess ||
                                  e->lhs->kind != ExprKind::kIdentifier;
       e = e->kind == ExprKind::kSelect ? e->base : e->lhs) {
    member = member || e->kind == ExprKind::kMemberAccess;
  }
  return member &&
         FindNamedProperty(t.obj->type, ctx, t.name, nullptr) == nullptr;
}

bool ResolveModeTarget(const Expr* expr, std::string_view method,
                       SimContext& ctx, Arena& arena, ModeTarget& out) {
  std::string_view obj_name;
  bool named = method == "rand_mode"
                   ? ExtractRandModeParts(expr, obj_name, out.name, out.element)
                   : ExtractConstraintModeParts(expr, obj_name, out.name);
  if (!named) {
    ScopedModeParts scoped;
    if (!ExtractScopedModeParts(expr, method, arena, scoped)) {
      return ResolveExprModeTarget(expr, method, ctx, arena, out);
    }
    obj_name = scoped.obj_name;
    out.name = scoped.name;
    out.element = scoped.element;
  }
  MethodCallParts parts;
  parts.var_name = obj_name;
  out.obj = ResolveRandomizeTarget(ctx, parts);
  if (named && out.obj != nullptr && out.element != nullptr &&
      PathThroughHandle(out, ctx)) {
    out = {};
    return ResolveExprModeTarget(expr, method, ctx, arena, out);
  }
  return out.obj != nullptr;
}

Logic4Vec NullTargetResult(const Expr* expr, Arena& arena) {
  return MakeLogic4VecVal(arena, expr->args.empty() ? 32 : 1, 0);
}

}  // namespace

bool IsModeMethodCall(const Expr* expr) {
  return ReceiverOfMethod(expr, "rand_mode") != nullptr ||
         ReceiverOfMethod(expr, "constraint_mode") != nullptr;
}

bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  ModeTarget target;
  if (!ResolveModeTarget(expr, "constraint_mode", ctx, arena, target)) {
    return false;
  }
  ClassObject* obj = target.obj;
  if (obj == nullptr) {
    out = NullTargetResult(expr, arena);
    return true;
  }
  std::string_view constraint_name = target.name;

  if (expr->args.empty()) {
    bool active = IsObjectConstraintActive(obj, constraint_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (constraint_name.empty()) {
    SetAllConstraintsActive(obj, on);
  } else {
    SetObjectConstraintActive(obj, constraint_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectRandMode(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  ModeTarget target;
  if (!ResolveModeTarget(expr, "rand_mode", ctx, arena, target)) return false;
  ClassObject* obj = target.obj;
  if (obj == nullptr) {
    out = NullTargetResult(expr, arena);
    return true;
  }
  std::string_view var_name = target.name;
  const Expr* element = target.element;
  std::string element_key;
  if (element != nullptr) {
    const Expr* root = VariablePathRoot(element);
    element_key = VariablePathKey(
        element, root != nullptr ? root : element->base, var_name, ctx, arena);
    var_name = element_key;
  }

  if (expr->args.empty()) {
    if (var_name.empty()) return false;
    bool active = IsObjectRandActive(obj, var_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (var_name.empty()) {
    SetAllRandVariablesActive(obj, on);
  } else {
    SetObjectRandActive(obj, var_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

}  // namespace delta
