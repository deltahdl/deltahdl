#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

namespace {

void FoldEnumMemberValues(const std::vector<EnumMember>& members,
                          std::vector<int64_t>& out) {
  int64_t next = 0;
  for (const auto& em : members) {
    if (em.value != nullptr) next = static_cast<int64_t>(em.value->int_val);
    out.push_back(next);
    ++next;
  }
}

void PopulateEnumDomain(const ClassMember* m, const ClassTypeInfo* level,
                        SimContext& ctx, RandVariable& var) {
  const DataType& dt = m->data_type;
  if (dt.kind == DataTypeKind::kEnum) {
    FoldEnumMemberValues(dt.enum_members, var.enum_values);
    return;
  }
  if (dt.kind != DataTypeKind::kNamed) return;
  for (const ClassTypeInfo* lvl = level; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl == nullptr) continue;
    for (const ClassMember* tm : lvl->decl->members) {
      if (tm->kind == ClassMemberKind::kTypedef &&
          tm->typedef_item != nullptr &&
          tm->typedef_item->typedef_type.kind == DataTypeKind::kEnum &&
          tm->typedef_item->name == dt.type_name) {
        FoldEnumMemberValues(tm->typedef_item->typedef_type.enum_members,
                             var.enum_values);
        return;
      }
    }
  }
  if (const EnumTypeInfo* info = ctx.FindEnumType(dt.type_name)) {
    for (const auto& em : info->members)
      var.enum_values.push_back(static_cast<int64_t>(em.value));
  }
}

bool DeclaredSignedness(const ClassMember* m, const ClassTypeInfo* level) {
  const DataType& dt = m->data_type;
  if (dt.kind != DataTypeKind::kNamed) return dt.is_signed;
  for (const ClassTypeInfo* lvl = level; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl == nullptr) continue;
    for (const ClassMember* tm : lvl->decl->members) {
      if (tm->kind == ClassMemberKind::kTypedef &&
          tm->typedef_item != nullptr && tm->typedef_item->name == dt.type_name)
        return tm->typedef_item->typedef_type.is_signed;
    }
  }
  return false;
}

}  // namespace

RandInfo BuildRandMember(const ClassMember* m, const ClassTypeInfo* level,
                         SimContext& ctx) {
  RandInfo info;
  info.name = std::string(m->name);
  info.level = level;
  info.is_static = m->is_static;
  info.var.name = info.name;
  info.var.qualifier =
      m->is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
  uint32_t width = EvalTypeWidth(m->data_type);
  if (width == 0 && m->data_type.kind == DataTypeKind::kNamed)
    width = ctx.FindTypeWidth(m->data_type.type_name);
  info.var.width = width == 0 ? 32 : width;
  PopulateEnumDomain(m, level, ctx, info.var);
  info.var.is_signed = DeclaredSignedness(m, level);
  info.var.BindDomainToDeclaredRange();
  if (m->data_type.kind == DataTypeKind::kReal ||
      m->data_type.kind == DataTypeKind::kShortreal ||
      m->data_type.kind == DataTypeKind::kRealtime) {
    info.var.is_real = true;
    info.var.real_min = -2147483648.0;
    info.var.real_max = 2147483648.0;
  }
  return info;
}

namespace {

void AddRandLeaves(const RandInfo& info,
                   const ClassTypeInfo::PropertyInfo& array, size_t dim,
                   const std::string& key, std::vector<RandInfo>& out) {
  if (dim == array.dim_sizes.size()) {
    RandInfo elem = info;
    elem.name = key;
    elem.var.name = key;
    elem.array_base = info.name;
    out.push_back(std::move(elem));
    return;
  }
  for (uint32_t i = 0; i < array.dim_sizes[dim]; ++i) {
    AddRandLeaves(info, array, dim + 1,
                  ClassArrayElementKey(key, array.dim_los[dim] + i), out);
  }
}

void AddRandMember(const ClassMember* m, const ClassTypeInfo* level,
                   SimContext& ctx, std::vector<RandInfo>& out) {
  if (IsQueuePropertyDecl(m, level, ctx) ||
      IsAssocPropertyDecl(m, level, ctx) ||
      AddRandStructMembers(m, level, ctx, out)) {
    return;
  }
  const auto* array = FindClassArrayProperty(level, m->name);
  if (array != nullptr && array->is_dynamic) return;
  RandInfo info = BuildRandMember(m, level, ctx);
  if (array == nullptr) {
    out.push_back(std::move(info));
    return;
  }
  if (array->dim_sizes.size() >= 2) {
    AddRandLeaves(info, *array, 0, info.name, out);
    return;
  }
  for (uint32_t i = 0; i < array->array_size; ++i) {
    RandInfo elem = info;
    elem.name = ClassArrayElementKey(m->name, array->array_lo + i);
    elem.var.name = elem.name;
    elem.array_base = info.name;
    elem.array_index = array->array_lo + static_cast<int64_t>(i);
    out.push_back(std::move(elem));
  }
}

bool TryComparisonConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                             RandomizeCtx& rc, ConstraintExpr& out,
                             bool fold = true) {
  if (!rel || rel->kind != ExprKind::kBinary || !rel->lhs || !rel->rhs)
    return false;
  ConstraintKind kind = ConstraintKind::kEqual;
  if (!ComparisonKind(rel->op, kind)) return false;
  const Expr* var_side = nullptr;
  const Expr* const_side = nullptr;
  bool mirror = false;
  if (rel->lhs->kind == ExprKind::kIdentifier &&
      FindRand(rands, rel->lhs->text) && !RefsRandVar(rel->rhs, rands)) {
    var_side = rel->lhs;
    const_side = rel->rhs;
  } else if (rel->rhs->kind == ExprKind::kIdentifier &&
             FindRand(rands, rel->rhs->text) && !RefsRandVar(rel->lhs, rands)) {
    var_side = rel->rhs;
    const_side = rel->lhs;
    mirror = true;
  }
  if (!var_side) return false;
  if (mirror) ComparisonKind(MirrorComparison(rel->op), kind);
  ConstraintEvalScope scope(rc.obj, rc.ctx);
  auto cv = EvalExpr(const_side, rc.ctx, rc.arena);
  int64_t c = cv.is_signed ? SignExtend(cv.ToUint64(), cv.width)
                           : static_cast<int64_t>(cv.ToUint64());
  out.kind = kind;
  out.var_name = std::string(var_side->text);
  out.lo = c;
  out.ref_vars.push_back(out.var_name);
  if (fold) FoldComparison(rands, var_side->text, kind, cv, c);
  return true;
}

static const ClassTypeInfo* StaticConstraintOwner(const ClassObject* obj,
                                                  std::string_view name) {
  for (const auto* lvl = obj ? obj->type : nullptr; lvl != nullptr;
       lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name)
        return m->is_static ? lvl : nullptr;
    }
  }
  return nullptr;
}

}  // namespace

void FoldComparison(std::vector<RandInfo>& rands, std::string_view name,
                    ConstraintKind kind, const Logic4Vec& cv, int64_t c) {
  auto* ri = FindRand(rands, name);
  if (ri == nullptr) return;
  if (ri->var.is_real) {
    FoldRealBound(*ri, kind,
                  cv.is_real ? RealVecToDouble(cv) : static_cast<double>(c));
    return;
  }
  FoldBound(*ri, kind, c);
}

bool AnyRefsRandVar(const std::vector<Expr*>& list,
                    std::vector<RandInfo>& rands) {
  for (const Expr* x : list) {
    if (RefsRandVar(x, rands)) return true;
  }
  return false;
}

static bool IsRandArray(std::string_view name, std::vector<RandInfo>& rands) {
  for (const auto& ri : rands) {
    if (ri.array_base == name) return true;
  }
  return false;
}

bool RefsRandVar(const Expr* e, std::vector<RandInfo>& rands) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    return FindRand(rands, e->text) != nullptr || IsRandArray(e->text, rands);
  }
  if (e->kind == ExprKind::kMemberAccess) {
    return e->lhs != nullptr && e->lhs->kind == ExprKind::kIdentifier &&
           e->lhs->text == "this" && e->rhs != nullptr &&
           e->rhs->kind == ExprKind::kIdentifier &&
           FindRand(rands, e->rhs->text) != nullptr;
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                          e->condition, e->true_expr, e->false_expr}) {
    if (RefsRandVar(sub, rands)) return true;
  }
  return AnyRefsRandVar(e->args, rands) || AnyRefsRandVar(e->elements, rands);
}

static void PromoteInlineRandomVariables(
    ClassObject* obj, SimContext& ctx,
    const std::unordered_set<std::string>& inline_random,
    std::vector<RandInfo>& rands) {
  for (const auto& nm : inline_random) {
    if (FindRand(rands, nm) != nullptr) continue;
    const ClassTypeInfo* lvl = nullptr;
    if (const ClassMember* m = FindNamedProperty(obj->type, ctx, nm, &lvl))
      AddRandMember(m, lvl, ctx, rands);
  }
}

static void AddInlineConstraintBlock(const InlineRandomizeCall& call,
                                     std::vector<RandInfo>& rands,
                                     RandomizeCtx& rc,
                                     ConstraintSolver& solver) {
  const Expr* expr = call.expr;
  if (expr == nullptr || !expr->with_has_parens) {
    AddConstraintMember(call.inline_block, rands, rc, solver);
    return;
  }
  std::unordered_set<std::string_view> listed(expr->with_restrict_ids.begin(),
                                              expr->with_restrict_ids.end());
  std::vector<RandInfo> listed_rands;
  for (const auto& ri : rands)
    if (listed.count(ri.name) != 0) listed_rands.push_back(ri);
  AddConstraintMember(call.inline_block, listed_rands, rc, solver);
}

static void BindRandcHistory(ClassObject* obj, RandInfo& ri) {
  if (ri.var.qualifier != RandQualifier::kRandc) return;
  std::shared_ptr<std::unordered_set<int64_t>>* slot =
      (ri.is_static && ri.level) ? &ri.level->static_randc_history[ri.name]
                                 : &obj->randc_history[ri.name];
  if (!*slot) *slot = std::make_shared<std::unordered_set<int64_t>>();
  ri.var.shared_randc_state = *slot;
  std::shared_ptr<std::vector<int64_t>>* domain =
      (ri.is_static && ri.level) ? &ri.level->static_randc_domain[ri.name]
                                 : &obj->randc_domain[ri.name];
  if (!*domain) *domain = std::make_shared<std::vector<int64_t>>();
  ri.var.shared_randc_domain = *domain;
}

void PrepareRandVariables(ClassObject* obj, std::vector<RandInfo>& rands,
                          const std::unordered_set<std::string>* inline_random,
                          ConstraintSolver& solver) {
  for (auto& ri : rands) {
    ri.var.CollapseEmptyDomain();
    BindRandcHistory(obj, ri);
    bool active = inline_random != nullptr ? inline_random->count(ri.name) != 0
                                           : IsObjectRandActive(obj, ri.name);
    if (!active) {
      const auto& held = ri.is_static && ri.level != nullptr
                             ? ri.level->static_properties
                             : obj->properties;
      auto pit = held.find(ri.name);
      if (pit != held.end())
        ri.var.value = ri.var.ValueFromBits(pit->second.ToUint64());
      ri.var.enabled = false;
    }
    solver.AddVariable(ri.var);
  }
}

static std::vector<std::string> HandleKeys(const ClassObject* obj,
                                           const std::string& name) {
  const auto* array = FindClassArrayProperty(obj->type, name);
  if (array == nullptr) return {name};
  std::vector<std::string> keys;
  int64_t lo = array->is_dynamic ? 0 : array->array_lo;
  uint32_t size = ClassArraySize(obj, *array);
  keys.reserve(size);
  for (uint32_t i = 0; i < size; ++i)
    keys.push_back(ClassArrayElementKey(name, lo + i));
  return keys;
}

static ClassObject* HeldObject(const ClassObject* obj, const std::string& key,
                               SimContext& ctx) {
  auto it = obj->properties.find(key);
  if (it == obj->properties.end()) return nullptr;
  uint64_t handle = it->second.ToUint64();
  return handle == kNullClassHandle ? nullptr : ctx.GetClassObject(handle);
}

std::vector<std::pair<std::string, ClassObject*>> ActiveRandObjectMembers(
    const ClassObject* obj, SimContext& ctx) {
  std::vector<std::string> object_members;
  CollectRandObjectMembers(obj->type, ctx, object_members);
  std::vector<std::pair<std::string, ClassObject*>> held;
  for (const auto& name : object_members) {
    if (!IsObjectRandActive(obj, name)) continue;
    for (auto& key : HandleKeys(obj, name)) {
      if (ClassObject* sub = HeldObject(obj, key, ctx))
        held.emplace_back(std::move(key), sub);
    }
  }
  return held;
}

std::string InlineReceiverName(const Expr* call) {
  if (call->lhs->kind != ExprKind::kMemberAccess) return {};
  return HierarchicalReferenceName(call->lhs->lhs);
}

bool SolveObject(ObjectSolve& part, const InlineRandomizeCall& call,
                 SimContext& ctx, Arena& arena) {
  ClassObject* obj = part.obj;
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(obj)());
  part.solver = std::make_unique<ConstraintSolver>(seed);
  ConstraintSolver& solver = *part.solver;
  part.rc = std::make_unique<RandomizeCtx>(RandomizeCtx{obj, ctx, arena});
  RandomizeCtx& rc = *part.rc;
  rc.solver = &solver;
  rc.inline_block = call.inline_block;
  rc.inline_receiver = InlineReceiverName(call.expr);

  std::vector<RandInfo>& rands = part.rands;
  CollectRandVariables(obj->type, ctx, rands);
  AddDynamicArrayVariables(rands, rc);
  if (call.inline_random != nullptr)
    PromoteInlineRandomVariables(obj, ctx, *call.inline_random, rands);
  CollectConstraintBlocks(obj->type, rands, rc, solver);
  if (call.inline_block != nullptr)
    AddInlineConstraintBlock(call, rands, rc, solver);
  PrepareRandVariables(obj, rands, call.inline_random, solver);
  return solver.SolveWith({});
}

void SetObjectConstraintActive(ClassObject* obj, std::string_view name,
                               bool active) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    owner->static_constraint_active[std::string(name)] = active;
    return;
  }
  obj->constraint_active[std::string(name)] = active;
}

std::unordered_map<std::string, bool>& RandModesOf(ClassObject* obj,
                                                   std::string_view name) {
  const ClassTypeInfo* owner = StaticRandOwner(obj, name);
  return owner != nullptr ? owner->static_rand_active : obj->rand_active;
}

void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active) {
  auto& modes = RandModesOf(obj, name);
  std::erase_if(modes, [name](const auto& entry) {
    const std::string& key = entry.first;
    return key.size() > name.size() && key.starts_with(name) &&
           (key[name.size()] == '[' || key[name.size()] == '.');
  });
  modes[std::string(name)] = active;
}

void CollectConstraintArgRefs(const Expr* e, bool in_arg,
                              std::unordered_set<std::string>& all_names,
                              std::unordered_set<std::string>& arg_names) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    all_names.insert(std::string(e->text));
    if (in_arg) arg_names.insert(std::string(e->text));
  }
  bool call = e->kind == ExprKind::kCall;
  CollectConstraintArgRefs(e->lhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->rhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->condition, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->true_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->false_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->base, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index_end, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->with_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->stream_range, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->repeat_count, in_arg, all_names, arg_names);
  for (const Expr* a : e->args)
    CollectConstraintArgRefs(a, call || in_arg, all_names, arg_names);
  for (const Expr* el : e->elements)
    CollectConstraintArgRefs(el, in_arg, all_names, arg_names);
}

bool IsClassHandleMember(const ClassMember* m, SimContext& ctx) {
  return m->data_type.kind == DataTypeKind::kNamed &&
         ctx.FindClassType(m->data_type.type_name) != nullptr;
}

static ConstraintExpr TranslateUnguarded(const Expr* rel,
                                         std::vector<RandInfo>& rands,
                                         RandomizeCtx& rc, bool fold) {
  ConstraintExpr ce;
  if (TryComparisonConstraint(rel, rands, rc, ce, fold)) return ce;
  if (TrySetMembershipConstraint(rel, rands, rc, ce)) return ce;
  if (TryImplicationConstraint(rel, rands, rc, ce)) return ce;
  if (TryConjunctionConstraint(rel, rands, rc, ce, fold)) return ce;
  if (TryArrayReductionConstraint(rel, rands, rc, ce)) return ce;
  return MakeCustomConstraint(rel, rands, rc);
}

ConstraintExpr TranslateRelation(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, bool fold) {
  ConstraintExpr joint;
  if (TryJointRelation(rel, rands, rc, fold, joint)) return joint;
  rel = ResolveArraySizes(rel, rc);
  rel = PackedMembersAsSelects(rel, rands, rc);
  ConstraintExpr ce = TranslateUnguarded(rel, rands, rc, fold);
  AttachConstraintGuard(
      rel, [&rands](const Expr* e) { return RefsRandVar(e, rands); }, rc.obj,
      rc, ce);
  return ce;
}

const ClassMember* FindNamedProperty(const ClassTypeInfo* type, SimContext& ctx,
                                     std::string_view name,
                                     const ClassTypeInfo** out_level) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          std::string_view(m->name) == name && !IsClassHandleMember(m, ctx)) {
        if (out_level != nullptr) *out_level = lvl;
        return m;
      }
    }
  }
  return nullptr;
}

std::string_view InlineRandomArgName(const Expr* arg) {
  if (arg == nullptr) return {};
  switch (arg->kind) {
    case ExprKind::kIdentifier:
      return arg->text;
    case ExprKind::kSelect:
      return InlineRandomArgName(arg->base);
    case ExprKind::kMemberAccess:
      return InlineRandomArgName(arg->rhs);
    default:
      return {};
  }
}

void InvokePreRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                        Arena& arena) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* pre =
          obj->ResolveMethodForType("pre_randomize", obj->type, &owner)) {
    ctx.PushMethodClass(owner);
    ExecInstanceMethodCall(pre, obj, expr, ctx, arena);
    ctx.PopMethodClass();
  }
}

ClassObject* ResolveRandomizeTarget(SimContext& ctx,
                                    const MethodCallParts& parts) {
  if (parts.var_name == "this") {
    auto* self = ctx.CurrentThis();
    return (self != nullptr && self->type != nullptr) ? self : nullptr;
  }
  if (ctx.GetVariableClassType(parts.var_name).empty()) return nullptr;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return nullptr;
  uint64_t handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return nullptr;
  ClassObject* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return nullptr;
  return obj;
}

Logic4Vec SolvedValue(const RandInfo& ri, const ConstraintSolver& solver,
                      const std::string& prefix, Arena& arena) {
  if (ri.var.is_real) {
    return MakeRealVec(arena, solver.GetRealValue(prefix + ri.name),
                       ri.var.width == 32 ? 32 : 64);
  }
  int64_t v = solver.GetValue(prefix + ri.name);
  Logic4Vec lv =
      MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
  lv.is_signed = ri.var.is_signed;
  return lv;
}

TokenKind MirrorComparison(TokenKind op) {
  switch (op) {
    case TokenKind::kGtEq:
      return TokenKind::kLtEq;
    case TokenKind::kLtEq:
      return TokenKind::kGtEq;
    case TokenKind::kGt:
      return TokenKind::kLt;
    case TokenKind::kLt:
      return TokenKind::kGt;
    default:
      return op;
  }
}

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name) {
  for (auto& ri : rands) {
    if (std::string_view(ri.name) == name) return &ri;
  }
  return nullptr;
}

void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && !IsClassHandleMember(m, ctx))
        AddRandMember(m, lvl, ctx, out);
    }
  }
}

bool ComparisonKind(TokenKind op, ConstraintKind& out) {
  switch (op) {
    case TokenKind::kGtEq:
      out = ConstraintKind::kGreaterEqual;
      return true;
    case TokenKind::kLtEq:
      out = ConstraintKind::kLessEqual;
      return true;
    case TokenKind::kGt:
      out = ConstraintKind::kGreaterThan;
      return true;
    case TokenKind::kLt:
      out = ConstraintKind::kLessThan;
      return true;
    case TokenKind::kEqEq:
      out = ConstraintKind::kEqual;
      return true;
    case TokenKind::kBangEq:
      out = ConstraintKind::kNotEqual;
      return true;
    default:
      return false;
  }
}

void FoldRealBound(RandInfo& ri, ConstraintKind kind, double c) {
  switch (kind) {
    case ConstraintKind::kGreaterEqual:
    case ConstraintKind::kGreaterThan:
      ri.var.real_min = std::max(ri.var.real_min, c);
      break;
    case ConstraintKind::kLessEqual:
    case ConstraintKind::kLessThan:
      ri.var.real_max = std::min(ri.var.real_max, c);
      break;
    case ConstraintKind::kEqual:
      ri.var.real_min = c;
      ri.var.real_max = c;
      break;
    default:
      break;
  }
}

void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c) {
  switch (kind) {
    case ConstraintKind::kGreaterEqual:
      ri.var.min_val = ri.var.DomainMax(ri.var.min_val, c);
      break;
    case ConstraintKind::kGreaterThan:
      ri.var.min_val = ri.var.DomainMax(
          ri.var.min_val, static_cast<int64_t>(static_cast<uint64_t>(c) + 1));
      break;
    case ConstraintKind::kLessEqual:
      ri.var.max_val = ri.var.DomainMin(ri.var.max_val, c);
      break;
    case ConstraintKind::kLessThan:
      ri.var.max_val = ri.var.DomainMin(
          ri.var.max_val, static_cast<int64_t>(static_cast<uint64_t>(c) - 1));
      break;
    default:
      break;
  }
}

bool IsObjectConstraintActive(const ClassObject* obj, std::string_view name) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    auto it = owner->static_constraint_active.find(std::string(name));
    return it == owner->static_constraint_active.end() ? true : it->second;
  }
  auto it = obj->constraint_active.find(std::string(name));
  return it == obj->constraint_active.end() ? true : it->second;
}

}  // namespace delta
