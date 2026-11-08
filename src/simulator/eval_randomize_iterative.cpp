#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

Expr* RewriteExpr(const Expr* e, const ExprRewrite& rewrite, Arena& arena) {
  if (e == nullptr) return nullptr;
  if (Expr* replaced = rewrite(e)) return replaced;
  auto* copy = arena.Create<Expr>(*e);
  copy->lhs = RewriteExpr(e->lhs, rewrite, arena);
  copy->rhs = RewriteExpr(e->rhs, rewrite, arena);
  copy->condition = RewriteExpr(e->condition, rewrite, arena);
  copy->true_expr = RewriteExpr(e->true_expr, rewrite, arena);
  copy->false_expr = RewriteExpr(e->false_expr, rewrite, arena);
  copy->base = RewriteExpr(e->base, rewrite, arena);
  copy->index = RewriteExpr(e->index, rewrite, arena);
  copy->index_end = RewriteExpr(e->index_end, rewrite, arena);
  copy->with_expr = RewriteExpr(e->with_expr, rewrite, arena);
  copy->stream_range = RewriteExpr(e->stream_range, rewrite, arena);
  copy->repeat_count = RewriteExpr(e->repeat_count, rewrite, arena);
  for (auto*& arg : copy->args) arg = RewriteExpr(arg, rewrite, arena);
  for (auto*& elem : copy->elements) elem = RewriteExpr(elem, rewrite, arena);
  for (auto*& key : copy->pattern_keys) key = RewriteExpr(key, rewrite, arena);
  return copy;
}

Expr* IdentifierExpr(std::string_view text, const Expr* like, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->range = like->range;
  id->text = {arena.AllocString(text.data(), text.size()), text.size()};
  return id;
}

namespace {

struct ForeachInstance {
  std::string_view loop_var;
  std::string_view array;
  int64_t index;
  int64_t lo;
  uint32_t count;
  RandomizeCtx& rc;
};

Expr* Instance(const Expr* e, const ForeachInstance& inst);

Expr* IndexLiteral(int64_t value, const Expr* like, Arena& arena) {
  std::string text = std::to_string(value);
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->range = like->range;
  literal->text = {arena.AllocString(text.data(), text.size()), text.size()};
  literal->int_val = static_cast<uint64_t>(value);
  return literal;
}

bool SelectsArray(const Expr* e, const ForeachInstance& inst) {
  if (e->kind != ExprKind::kSelect || e->index_end != nullptr ||
      e->base == nullptr || e->index == nullptr) {
    return false;
  }
  if (e->base->kind == ExprKind::kIdentifier)
    return e->base->text == inst.array;
  return e->base->kind == ExprKind::kMemberAccess &&
         HierarchicalReferenceName(e->base) == inst.array;
}

bool IsLiteralExpr(const Expr* e) {
  if (e->kind == ExprKind::kIntegerLiteral) return true;
  if (e->kind != ExprKind::kBinary && e->kind != ExprKind::kUnary) return false;
  return (e->lhs == nullptr || IsLiteralExpr(e->lhs)) &&
         (e->rhs == nullptr || IsLiteralExpr(e->rhs));
}

Expr* ElementSelect(const Expr* e, const ForeachInstance& inst) {
  Expr* index = Instance(e->index, inst);
  if (!IsLiteralExpr(index)) return nullptr;
  Logic4Vec value = EvalExpr(index, inst.rc.ctx, inst.rc.arena);
  int64_t at = value.is_signed ? SignExtend(value.ToUint64(), value.width)
                               : static_cast<int64_t>(value.ToUint64());
  if (at < inst.lo || at >= inst.lo + static_cast<int64_t>(inst.count))
    return nullptr;
  return IdentifierExpr(ClassArrayElementKey(inst.array, at), e, inst.rc.arena);
}

Expr* Instance(const Expr* e, const ForeachInstance& inst) {
  return RewriteExpr(
      e,
      [&inst](const Expr* n) -> Expr* {
        if (n->kind == ExprKind::kIdentifier && n->text == inst.loop_var)
          return IndexLiteral(inst.index, n, inst.rc.arena);
        return SelectsArray(n, inst) ? ElementSelect(n, inst) : nullptr;
      },
      inst.rc.arena);
}

const std::vector<Expr*>& ForeachInstances(const ConstraintForeachRef& ref,
                                           std::string_view array, int64_t lo,
                                           uint32_t count, RandomizeCtx& rc) {
  auto& cached = rc.obj->type->foreach_instances[&ref];
  if (cached.count == count && !cached.relations.empty()) {
    return cached.relations;
  }
  cached.count = count;
  cached.relations.clear();
  if (ref.loop_vars.size() != 1 || ref.loop_vars[0].empty()) {
    return cached.relations;
  }
  for (uint32_t i = 0; i < count; ++i) {
    ForeachInstance inst{
        ref.loop_vars[0], array, lo + static_cast<int64_t>(i), lo, count, rc};
    for (const Expr* rel : ref.body)
      cached.relations.push_back(Instance(rel, inst));
  }
  return cached.relations;
}

std::string LeafKey(const Expr* e, std::string_view array, size_t dims,
                    RandomizeCtx& rc) {
  std::vector<const Expr*> indices;
  while (e != nullptr && e->kind == ExprKind::kSelect &&
         e->index_end == nullptr && e->index != nullptr) {
    indices.push_back(e->index);
    e = e->base;
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier || e->text != array ||
      indices.size() != dims) {
    return {};
  }
  std::string key(array);
  for (auto it = indices.rbegin(); it != indices.rend(); ++it) {
    if (!IsLiteralExpr(*it)) return {};
    Logic4Vec value = EvalExpr(*it, rc.ctx, rc.arena);
    key = ClassArrayElementKey(
        key, value.is_signed ? SignExtend(value.ToUint64(), value.width)
                             : static_cast<int64_t>(value.ToUint64()));
  }
  return key;
}

void IndexCombinations(const ConstraintForeachRef& ref,
                       const std::vector<uint32_t>& los,
                       const std::vector<uint32_t>& sizes,
                       std::vector<int64_t>& index,
                       std::vector<std::vector<int64_t>>& out) {
  size_t dim = index.size();
  if (dim == ref.loop_vars.size() || dim == sizes.size()) {
    out.push_back(index);
    return;
  }
  uint32_t count = ref.loop_vars[dim].empty() ? 1 : sizes[dim];
  for (uint32_t i = 0; i < count; ++i) {
    index.push_back(los[dim] + static_cast<int64_t>(i));
    IndexCombinations(ref, los, sizes, index, out);
    index.pop_back();
  }
}

Expr* LoopIndexLiteral(const Expr* n, const ConstraintForeachRef& ref,
                       const std::vector<int64_t>& index, Arena& arena) {
  if (n->kind != ExprKind::kIdentifier) return nullptr;
  for (size_t d = 0; d < index.size(); ++d) {
    if (!ref.loop_vars[d].empty() && n->text == ref.loop_vars[d])
      return IndexLiteral(index[d], n, arena);
  }
  return nullptr;
}

void AppendMultiForeachInstances(const ConstraintForeachRef& ref,
                                 const ClassTypeInfo::PropertyInfo& array,
                                 RandomizeCtx& rc, std::vector<Expr*>& out) {
  std::vector<int64_t> index;
  std::vector<std::vector<int64_t>> combinations;
  IndexCombinations(ref, array.dim_los, array.dim_sizes, index, combinations);
  size_t dims = array.dim_sizes.size();
  auto leaf = [&](const Expr* n) -> Expr* {
    std::string key = LeafKey(n, ref.array_name, dims, rc);
    return key.empty() ? nullptr : IdentifierExpr(key, n, rc.arena);
  };
  for (const auto& combination : combinations) {
    auto instance = [&](const Expr* n) {
      return LoopIndexLiteral(n, ref, combination, rc.arena);
    };
    for (const Expr* rel : ref.body) {
      out.push_back(
          RewriteExpr(RewriteExpr(rel, instance, rc.arena), leaf, rc.arena));
    }
  }
}

void AppendStateMultiForeachInstances(const ConstraintForeachRef& ref,
                                      const ArrayInfo& info, RandomizeCtx& rc,
                                      std::vector<Expr*>& out) {
  std::vector<int64_t> index;
  std::vector<std::vector<int64_t>> combinations;
  IndexCombinations(ref, info.dim_los, info.dim_sizes, index, combinations);
  for (const auto& combination : combinations) {
    auto instance = [&](const Expr* n) {
      return LoopIndexLiteral(n, ref, combination, rc.arena);
    };
    for (const Expr* rel : ref.body)
      out.push_back(RewriteExpr(rel, instance, rc.arena));
  }
}

struct IteratedElements {
  int64_t lo = 0;
  uint32_t count = 0;
  std::string size_var;
};

IteratedElements ElementsOf(const ClassTypeInfo::PropertyInfo& array,
                            std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  IteratedElements out;
  out.lo = array.is_dynamic ? 0 : array.array_lo;
  uint32_t rand_count = 0;
  for (const auto& ri : rands) {
    if (ri.array_base == array.name && !ri.var.is_array_size) ++rand_count;
  }
  out.count = rand_count > 0 ? rand_count : ClassArraySize(rc.obj, array);
  if (array.is_dynamic && FindRand(rands, ClassArraySizeKey(array.name)))
    out.size_var = ClassArraySizeKey(array.name);
  return out;
}

Expr* AssocKeyLiteral(const RandInfo& ri, std::string_view array,
                      const Expr* like, Arena& arena) {
  bool string_key =
      ri.name.size() > array.size() + 1 && ri.name[array.size() + 1] == '"';
  if (!string_key) {
    bool fits = AssocIndex(ri.int_key.Low()) == ri.int_key;
    return fits ? IndexLiteral(ri.int_key.Low(), like, arena)
                : LiteralOfValue(ri.int_key.ToSignedVec(arena), arena);
  }
  std::string text = "\"" + ri.str_key + "\"";
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kStringLiteral;
  literal->range = like->range;
  literal->text = {arena.AllocString(text.data(), text.size()), text.size()};
  return literal;
}

Expr* AssocInstance(const Expr* n, const RandInfo& ri,
                    const ConstraintForeachRef& ref, Arena& arena) {
  std::string_view var = ref.loop_vars[0];
  if (n->kind == ExprKind::kSelect && n->index_end == nullptr &&
      n->base != nullptr && n->base->kind == ExprKind::kIdentifier &&
      n->base->text == ref.array_name && n->index != nullptr &&
      n->index->kind == ExprKind::kIdentifier && n->index->text == var) {
    return IdentifierExpr(ri.name, n, arena);
  }
  if (n->kind == ExprKind::kIdentifier && n->text == var)
    return AssocKeyLiteral(ri, ref.array_name, n, arena);
  return nullptr;
}

bool AppendAssocForeachInstances(const ConstraintForeachRef& ref,
                                 std::vector<RandInfo>& rands, RandomizeCtx& rc,
                                 std::vector<Expr*>& out) {
  if (ref.loop_vars.size() != 1 || ref.loop_vars[0].empty()) return false;
  bool any = false;
  for (const auto& ri : rands) {
    if (!ri.in_assoc || ri.array_base != ref.array_name) continue;
    any = true;
    auto instance = [&](const Expr* n) {
      return AssocInstance(n, ri, ref, rc.arena);
    };
    for (const Expr* rel : ref.body)
      out.push_back(RewriteExpr(rel, instance, rc.arena));
  }
  return any;
}

bool StructDynamicElements(std::string_view name, std::vector<RandInfo>& rands,
                           IteratedElements& out, std::string_view& path) {
  uint32_t count = 0;
  for (const auto& ri : rands) {
    std::string_view base = ri.array_base;
    if (ri.dyn_field == nullptr || base.size() <= name.size() ||
        base.substr(base.size() - name.size()) != name ||
        base[base.size() - name.size() - 1] != '.') {
      continue;
    }
    path = ri.array_base;
    ++count;
  }
  out.lo = 0;
  out.count = count;
  return count > 0;
}

bool QueueElements(std::string_view name, std::vector<RandInfo>& rands,
                   IteratedElements& out) {
  uint32_t count = 0;
  for (const auto& ri : rands) {
    if (ri.in_queue && ri.array_base == name && !ri.var.is_array_size) ++count;
  }
  if (count == 0) return false;
  out.lo = 0;
  out.count = count;
  if (FindRand(rands, ClassArraySizeKey(name)) != nullptr)
    out.size_var = ClassArraySizeKey(name);
  return true;
}

bool StateArrayElements(std::string_view name, RandomizeCtx& rc,
                        IteratedElements& out) {
  if (const QueueObject* queue = rc.ctx.FindQueue(name)) {
    out.lo = 0;
    out.count = static_cast<uint32_t>(queue->elements.size());
    return true;
  }
  const ArrayInfo* info = rc.ctx.FindArrayInfo(name);
  if (info == nullptr || info->dim_sizes.size() >= 2) return false;
  out.lo = info->lo;
  out.count = info->size;
  return true;
}

bool StringText(std::string_view name, RandomizeCtx& rc, std::string& out) {
  const auto* prop = rc.obj->type->FindProperty(name);
  if (prop != nullptr && prop->is_string) {
    out = Logic4VecToString(rc.obj->GetProperty(name, rc.arena));
  } else if (rc.ctx.IsStringVariable(name)) {
    out = Logic4VecToString(rc.ctx.FindVariable(name)->value);
  } else {
    return false;
  }
  return true;
}

Expr* CharacterInstance(const Expr* e, const ForeachInstance& inst,
                        const std::string& text);

Expr* CharacterSelect(const Expr* e, const ForeachInstance& inst,
                      const std::string& text) {
  Expr* index = CharacterInstance(e->index, inst, text);
  if (!IsLiteralExpr(index)) return nullptr;
  const uint64_t kAt = EvalExpr(index, inst.rc.ctx, inst.rc.arena).ToUint64();
  const int64_t kChar =
      kAt < text.size() ? static_cast<unsigned char>(text[kAt]) : 0;
  return IndexLiteral(kChar, e, inst.rc.arena);
}

Expr* CharacterInstance(const Expr* e, const ForeachInstance& inst,
                        const std::string& text) {
  return RewriteExpr(
      e,
      [&inst, &text](const Expr* n) -> Expr* {
        if (n->kind == ExprKind::kIdentifier && n->text == inst.loop_var)
          return IndexLiteral(inst.index, n, inst.rc.arena);
        return SelectsArray(n, inst) ? CharacterSelect(n, inst, text) : nullptr;
      },
      inst.rc.arena);
}

std::vector<Expr*> StringForeachInstances(const ConstraintForeachRef& ref,
                                          const std::string& text,
                                          RandomizeCtx& rc) {
  std::vector<Expr*> out;
  const auto kCount = static_cast<uint32_t>(text.size());
  for (uint32_t i = 0; i < kCount; ++i) {
    const ForeachInstance kInst{
        ref.loop_vars.front(), ref.array_name, i, 0, kCount, rc};
    for (const Expr* rel : ref.body)
      out.push_back(CharacterInstance(rel, kInst, text));
  }
  return out;
}

bool ReductionOp(std::string_view method, ArrayReductionOp& out) {
  if (method == "sum") {
    out = ArrayReductionOp::kSum;
  } else if (method == "product") {
    out = ArrayReductionOp::kProduct;
  } else if (method == "and") {
    out = ArrayReductionOp::kAnd;
  } else if (method == "or") {
    out = ArrayReductionOp::kOr;
  } else if (method == "xor") {
    out = ArrayReductionOp::kXor;
  } else {
    return false;
  }
  return true;
}

std::vector<std::string> ElementNames(std::string_view array,
                                      std::vector<RandInfo>& rands) {
  std::vector<std::string> names;
  for (const auto& ri : rands) {
    if (ri.array_base == array && !ri.var.is_array_size)
      names.push_back(ri.name);
  }
  return names;
}

bool ArgsAreIteratorNames(const Expr* e) {
  return std::all_of(e->args.begin(), e->args.end(), [](const Expr* arg) {
    return arg != nullptr && arg->kind == ExprKind::kIdentifier;
  });
}

bool ReductionCall(const Expr* e, std::vector<RandInfo>& rands,
                   ArrayReductionOp& op, std::vector<std::string>& elements) {
  if (e == nullptr || e->kind != ExprKind::kCall || !ArgsAreIteratorNames(e) ||
      e->lhs == nullptr || e->lhs->kind != ExprKind::kMemberAccess ||
      e->lhs->is_scope_resolution || e->lhs->lhs == nullptr ||
      e->lhs->rhs == nullptr || e->lhs->lhs->kind != ExprKind::kIdentifier ||
      e->lhs->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!ReductionOp(e->lhs->rhs->text, op)) return false;
  elements = ElementNames(e->lhs->lhs->text, rands);
  return !elements.empty();
}

int64_t BoundValue(const Expr* e, RandomizeCtx& rc) {
  ConstraintEvalScope scope(rc.obj, rc.ctx);
  Logic4Vec value = EvalExpr(e, rc.ctx, rc.arena);
  return value.is_signed ? SignExtend(value.ToUint64(), value.width)
                         : static_cast<int64_t>(value.ToUint64());
}

std::function<int64_t(int64_t)> WithFunction(const Expr* call,
                                             const RandVariable& elem,
                                             RandomizeCtx& rc,
                                             Logic4Vec& result) {
  IterNames names = ExtractIterNames(call);
  std::string_view iter = names.iter_name;
  rc.ctx.PushScope();
  Variable* item = rc.ctx.CreateLocalVariable(iter, elem.width, elem.is_signed);
  rc.ctx.PopScope();
  auto evaluate = [call, iter, item, &rc](int64_t v) {
    rc.ctx.PushScope();
    rc.ctx.BindLocalVariable(iter, item);
    SetLocalWords(item->value, v);
    Logic4Vec value;
    {
      ConstraintEvalScope scope(rc.obj, rc.ctx);
      value = EvalExpr(call->with_expr, rc.ctx, rc.arena);
    }
    rc.ctx.PopScope();
    return value;
  };
  result = evaluate(0);
  return [evaluate](int64_t v) {
    Logic4Vec value = evaluate(v);
    return value.is_signed ? SignExtend(value.ToUint64(), value.width)
                           : static_cast<int64_t>(value.ToUint64());
  };
}

}  // namespace

bool TryArrayReductionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr) {
    return false;
  }
  ArrayReductionOp op = ArrayReductionOp::kSum;
  std::vector<std::string> elements;
  bool call_on_left = ReductionCall(rel->lhs, rands, op, elements);
  if (!call_on_left && !ReductionCall(rel->rhs, rands, op, elements))
    return false;
  const Expr* other = call_on_left ? rel->rhs : rel->lhs;
  if (RefsRandVar(other, rands)) return false;
  ConstraintKind cmp = ConstraintKind::kEqual;
  if (!ComparisonKind(call_on_left ? rel->op : MirrorComparison(rel->op), cmp))
    return false;
  out.kind = ConstraintKind::kArrayReduction;
  out.reduce_op = op;
  out.reduce_cmp = cmp;
  out.lo = BoundValue(other, rc);
  const RandInfo* elem = FindRand(rands, elements.front());
  out.reduce_width = elem != nullptr ? elem->var.width : 32;
  const Expr* call = call_on_left ? rel->lhs : rel->rhs;
  if (call->with_expr != nullptr && elem != nullptr) {
    Logic4Vec result;
    out.reduce_with = WithFunction(call, elem->var, rc, result);
    out.reduce_width = result.width;
  }
  out.reduce_vars = elements;
  out.ref_vars = std::move(elements);
  std::string size_var =
      ClassArraySizeKey(elem != nullptr ? elem->array_base : std::string());
  if (FindRand(rands, size_var) != nullptr) {
    out.size_var = size_var;
    out.ref_vars.push_back(size_var);
  }
  return true;
}

struct ForeachBuild {
  const std::vector<Expr*>& instances;
  size_t rel_count;
  const IteratedElements& elems;
  bool fold;
};

ConstraintExpr SizedForeach(const ForeachBuild& build, size_t rel,
                            std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kForeach;
  ce.size_var = build.elems.size_var;
  ce.ref_vars.push_back(build.elems.size_var);
  for (size_t i = rel; i < build.instances.size(); i += build.rel_count) {
    ConstraintExpr sub =
        TranslateRelation(build.instances[i], rands, rc, build.fold);
    for (const auto& name : sub.ref_vars) ce.ref_vars.push_back(name);
    ce.sub_constraints.push_back(std::move(sub));
  }
  return ce;
}

namespace {

void AddInstances(const std::vector<Expr*>& instances,
                  std::vector<RandInfo>& rands, RandomizeCtx& rc,
                  ConstraintBlock& block) {
  for (const Expr* rel : instances) {
    block.constraints.push_back(
        TranslateRelation(rel, rands, rc, block.enabled));
  }
}

struct Iterated {
  IteratedElements elems;
  std::string_view element_array;
};

bool IteratedOf(const ConstraintForeachRef& ref,
                const ClassTypeInfo::PropertyInfo* array,
                std::vector<RandInfo>& rands, RandomizeCtx& rc, Iterated& out) {
  if (array != nullptr) {
    out.elems = ElementsOf(*array, rands, rc);
    out.element_array = ref.array_name;
    return true;
  }
  if (QueueElements(ref.array_name, rands, out.elems)) {
    out.element_array = ref.array_name;
    return true;
  }
  if (StructDynamicElements(ref.array_name, rands, out.elems,
                            out.element_array)) {
    return true;
  }
  return StateArrayElements(ref.array_name, rc, out.elems);
}

void AddForeachConstraint(const ConstraintForeachRef& ref,
                          std::vector<RandInfo>& rands, RandomizeCtx& rc,
                          ConstraintBlock& block) {
  const auto* array = FindClassArrayProperty(rc.obj->type, ref.array_name);
  std::vector<Expr*> instances;
  if (array != nullptr && array->dim_sizes.size() >= 2 &&
      ref.loop_vars.size() >= 2) {
    AppendMultiForeachInstances(ref, *array, rc, instances);
    AddInstances(instances, rands, rc, block);
    return;
  }
  if (array == nullptr &&
      AppendAssocForeachInstances(ref, rands, rc, instances)) {
    AddInstances(instances, rands, rc, block);
    return;
  }
  const ArrayInfo* state =
      array == nullptr ? rc.ctx.FindArrayInfo(ref.array_name) : nullptr;
  if (state != nullptr && state->dim_sizes.size() >= 2 &&
      ref.loop_vars.size() >= 2) {
    AppendStateMultiForeachInstances(ref, *state, rc, instances);
    AddInstances(instances, rands, rc, block);
    return;
  }
  std::string text;
  if (StringText(ref.array_name, rc, text)) {
    AddInstances(StringForeachInstances(ref, text, rc), rands, rc, block);
    return;
  }
  Iterated it;
  if (!IteratedOf(ref, array, rands, rc, it)) return;
  ForeachBuild build{
      ForeachInstances(ref, it.element_array, it.elems.lo, it.elems.count, rc),
      ref.body.size(), it.elems, block.enabled};
  if (it.elems.size_var.empty()) {
    AddInstances(build.instances, rands, rc, block);
    return;
  }
  for (size_t rel = 0; rel < ref.body.size(); ++rel)
    block.constraints.push_back(SizedForeach(build, rel, rands, rc));
}

}  // namespace

void AddForeachConstraints(const ClassMember* m, std::vector<RandInfo>& rands,
                           RandomizeCtx& rc, ConstraintBlock& block) {
  for (const auto& ref : m->constraint_foreach_refs) {
    if (!ref.body.empty()) AddForeachConstraint(ref, rands, rc, block);
  }
}

}  // namespace delta
