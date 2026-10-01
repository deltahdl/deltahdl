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
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// 18.5.7: iterative constraints, which constrain an arrayed variable through
// a loop variable and an indexing expression -- a foreach iterative constraint
// (18.5.7.1) -- or through an array reduction method (18.5.7.2).

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

// The substitution one instance of a foreach constraint_set makes: the loop
// variable stands for `index`, and a select of `array` at the loop variable,
// or at any index expression free of names that reads as one of the `count`
// indexes from `lo`, names the element at that index.
struct ForeachInstance {
  std::string_view loop_var;
  std::string_view array;
  int64_t index;
  int64_t lo;
  uint32_t count;
  RandomizeCtx& rc;
};

Expr* Instance(const Expr* e, const ForeachInstance& inst);

// A decimal literal of `value`, which the loop variable's index is.
Expr* IndexLiteral(int64_t value, const Expr* like, Arena& arena) {
  std::string text = std::to_string(value);
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->range = like->range;
  literal->text = {arena.AllocString(text.data(), text.size()), text.size()};
  literal->int_val = static_cast<uint64_t>(value);
  return literal;
}

// Whether `e` is a single-index select of the iterated array.
bool SelectsArray(const Expr* e, const ForeachInstance& inst) {
  return e->kind == ExprKind::kSelect && e->index_end == nullptr &&
         e->base != nullptr && e->base->kind == ExprKind::kIdentifier &&
         e->base->text == inst.array && e->index != nullptr;
}

// Whether `e` is written over literals alone, so that it reads the same
// whatever is in scope: a literal, or an operator over such operands.
bool IsLiteralExpr(const Expr* e) {
  if (e->kind == ExprKind::kIntegerLiteral) return true;
  if (e->kind != ExprKind::kBinary && e->kind != ExprKind::kUnary) return false;
  return (e->lhs == nullptr || IsLiteralExpr(e->lhs)) &&
         (e->rhs == nullptr || IsLiteralExpr(e->rhs));
}

// 18.5.7.1: a select of the iterated array whose instanced index reads as
// one of its elements -- `A[i]` and the clause's `A[k+1]` -- as the
// identifier of that element's key, which the trial binds to the element's
// variable; null for a select at an index over a name, a state variable's
// or another array's, which the trial reads against the elements it binds,
// or at one beyond the elements, which reads the element type's default.
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

// 18.5.7.1: `e` as one instance of the constraint_set reads it: the loop
// variable as the index, a select of the array at an element's index as the
// element's variable, and anything else as written over instanced operands.
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

// 18.5.7.1: the relations `ref` instances over `count` elements of the array
// it iterates from the index `lo`, a select of `array` at an element's index
// read as the element's variable, one instance of each relation of the
// constraint_set per element in index order, built once per class and count
// and kept on the class. A header naming more than one loop variable
// iterates a dimension the object does not model, and instances nothing.
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

// §18.5.7.1: the leaf key, `m[1][2]`, a select chain of the array `array`
// of `dims` unpacked dimensions reads where every index is written over
// literals; empty for any other expression.
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

// §18.5.7.1: the relations of `ref`, whose header names a loop variable for
// each of several dimensions of the array property `array`, instanced once
// per combination of the indices those dimensions declare, outermost first,
// each loop variable read as its index and each select of a leaf element as
// the element's variable, appended to `out`. A dimension the header leaves
// unnamed is not iterated.
void AppendMultiForeachInstances(const ConstraintForeachRef& ref,
                                 const ClassTypeInfo::PropertyInfo& array,
                                 size_t dim, std::vector<int64_t>& index,
                                 RandomizeCtx& rc, std::vector<Expr*>& out) {
  size_t dims = array.dim_sizes.size();
  if (dim == ref.loop_vars.size() || dim == dims) {
    auto instance = [&](const Expr* n) -> Expr* {
      for (size_t d = 0; d < index.size(); ++d) {
        if (n->kind == ExprKind::kIdentifier && !ref.loop_vars[d].empty() &&
            n->text == ref.loop_vars[d]) {
          return IndexLiteral(index[d], n, rc.arena);
        }
      }
      return nullptr;
    };
    auto leaf = [&](const Expr* n) -> Expr* {
      std::string key = LeafKey(n, ref.array_name, dims, rc);
      return key.empty() ? nullptr : IdentifierExpr(key, n, rc.arena);
    };
    for (const Expr* rel : ref.body) {
      out.push_back(
          RewriteExpr(RewriteExpr(rel, instance, rc.arena), leaf, rc.arena));
    }
    return;
  }
  if (ref.loop_vars[dim].empty()) {
    index.push_back(array.dim_los[dim]);
    AppendMultiForeachInstances(ref, array, dim + 1, index, rc, out);
    index.pop_back();
    return;
  }
  for (uint32_t i = 0; i < array.dim_sizes[dim]; ++i) {
    index.push_back(array.dim_los[dim] + static_cast<int64_t>(i));
    AppendMultiForeachInstances(ref, array, dim + 1, index, rc, out);
    index.pop_back();
  }
}

// 18.5.7.1: the elements of the array `array` a foreach iterates: the rand
// element variables where the member is random, else the elements the
// object holds; `size_var` names the variable holding a dynamic array's
// size where a randomize() solves it, and stays empty where the size is a
// fact about the object.
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

// §18.4 with §18.5.7.1: the relations of `ref`, a foreach over the rand
// associative array it names, instanced once per key the array holds, the
// loop variable read as the key and the select of the array at it as the
// element's variable, appended to `out`; false where the array holds no
// element of the solve.
bool AppendAssocForeachInstances(const ConstraintForeachRef& ref,
                                 std::vector<RandInfo>& rands, RandomizeCtx& rc,
                                 std::vector<Expr*>& out) {
  if (ref.loop_vars.size() != 1 || ref.loop_vars[0].empty()) return false;
  std::string_view var = ref.loop_vars[0];
  bool any = false;
  for (const auto& ri : rands) {
    if (!ri.in_assoc || ri.array_base != ref.array_name) continue;
    any = true;
    bool string_key = ri.name.size() > ref.array_name.size() + 1 &&
                      ri.name[ref.array_name.size() + 1] == '"';
    auto key = [&](const Expr* like) -> Expr* {
      if (!string_key) return IndexLiteral(ri.int_key, like, rc.arena);
      std::string text = "\"" + ri.str_key + "\"";
      auto* literal = rc.arena.Create<Expr>();
      literal->kind = ExprKind::kStringLiteral;
      literal->range = like->range;
      literal->text = {rc.arena.AllocString(text.data(), text.size()),
                       text.size()};
      return literal;
    };
    auto instance = [&](const Expr* n) -> Expr* {
      if (n->kind == ExprKind::kSelect && n->index_end == nullptr &&
          n->base != nullptr && n->base->kind == ExprKind::kIdentifier &&
          n->base->text == ref.array_name && n->index != nullptr &&
          n->index->kind == ExprKind::kIdentifier && n->index->text == var) {
        return IdentifierExpr(ri.name, n, rc.arena);
      }
      if (n->kind == ExprKind::kIdentifier && n->text == var) return key(n);
      return nullptr;
    };
    for (const Expr* rel : ref.body)
      out.push_back(RewriteExpr(rel, instance, rc.arena));
  }
  return any;
}

// §18.4 with §18.5.7.1: the elements of the rand queue `name`, the element
// variables AddDynamicArrayVariables made for it from index 0, and the size
// variable where a randomize() solves its size; false where it made none.
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

// §18.7 with §18.5.7.1: the elements of an array no property of the object
// names, one of the scope containing an inline constraint's call, which a
// foreach iterates as state: a fixed array of one unpacked dimension from
// its low index, or a queue or dynamic array from 0. False for any other
// name.
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

// 18.5.7.2: the operand a reduction method named `method` joins the elements
// by; false for a name that is no reduction method.
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

// The element variables of the rand array member `array`, in index order.
std::vector<std::string> ElementNames(std::string_view array,
                                      std::vector<RandInfo>& rands) {
  std::vector<std::string> names;
  for (const auto& ri : rands) {
    if (ri.array_base == array && !ri.var.is_array_size)
      names.push_back(ri.name);
  }
  return names;
}

// Whether every argument of the call `e` is an identifier, which is what
// the iterator arguments of an array method call are (7.12).
bool ArgsAreIteratorNames(const Expr* e) {
  return std::all_of(e->args.begin(), e->args.end(), [](const Expr* arg) {
    return arg != nullptr && arg->kind == ExprKind::kIdentifier;
  });
}

// 18.5.7.2: `e` as a reduction method called on a rand array member, with a
// with clause or without one, filling the method's operand and the element
// variables; false for any other expression.
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

// The value `e`, free of random variables, takes in the object's scope, in
// the signed reading its own signedness gives it.
int64_t BoundValue(const Expr* e, RandomizeCtx& rc) {
  ConstraintEvalScope scope(rc.obj, rc.ctx);
  Logic4Vec value = EvalExpr(e, rc.ctx, rc.arena);
  return value.is_signed ? SignExtend(value.ToUint64(), value.width)
                         : static_cast<int64_t>(value.ToUint64());
}

// 18.5.7.2: the with clause of the reduction call `call` as the function of
// an element's value the solver folds, the iterator bound to the value in
// the element type `elem` declares and the expression evaluated in the
// object's scope, through one local made here and bound per evaluation, a
// fold being evaluated some hundred times per solve. `result` receives the
// value the clause maps the element type's zero to, whose width and
// signedness are the clause's expression's, which the fold is held to.
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
  // 18.5.7.2: the result is of the element type, or, where the call carries
  // a with clause, of the type of the clause's expression, so the fold is
  // held to that type's width.
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
  // 18.5.7.2: over a dynamic array whose size is solved, the elements below
  // the size drawn, the size constraints being solved first.
  std::string size_var =
      ClassArraySizeKey(elem != nullptr ? elem->array_base : std::string());
  if (FindRand(rands, size_var) != nullptr) {
    out.size_var = size_var;
    out.ref_vars.push_back(size_var);
  }
  return true;
}

// One foreach constraint being built into a block: its relations instanced
// over the elements, `rel_count` of them per element in index order, the
// elements iterated, and whether a relation folds its variable's domain.
struct ForeachBuild {
  const std::vector<Expr*>& instances;
  size_t rel_count;
  const IteratedElements& elems;
  bool fold;
};

// 18.5.7.1: the relation at `rel` of a foreach constraint_set over a dynamic
// array whose size is solved, as the solver's foreach over its instances in
// index order, of which the ones below the size drawn are imposed, the size
// being a state variable there.
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

void AddForeachConstraints(const ClassMember* m, std::vector<RandInfo>& rands,
                           RandomizeCtx& rc, ConstraintBlock& block) {
  for (const auto& ref : m->constraint_foreach_refs) {
    if (ref.body.empty()) continue;
    const auto* array = FindClassArrayProperty(rc.obj->type, ref.array_name);
    if (array != nullptr && array->dim_sizes.size() >= 2 &&
        ref.loop_vars.size() >= 2) {
      std::vector<int64_t> index;
      std::vector<Expr*> instances;
      AppendMultiForeachInstances(ref, *array, 0, index, rc, instances);
      for (const Expr* rel : instances) {
        block.constraints.push_back(
            TranslateRelation(rel, rands, rc, /*fold=*/block.enabled));
      }
      continue;
    }
    std::vector<Expr*> assoc;
    if (array == nullptr &&
        AppendAssocForeachInstances(ref, rands, rc, assoc)) {
      for (const Expr* rel : assoc) {
        block.constraints.push_back(
            TranslateRelation(rel, rands, rc, /*fold=*/block.enabled));
      }
      continue;
    }
    IteratedElements elems;
    bool rand_queue =
        array == nullptr && QueueElements(ref.array_name, rands, elems);
    if (array != nullptr) {
      elems = ElementsOf(*array, rands, rc);
    } else if (!rand_queue && !StateArrayElements(ref.array_name, rc, elems)) {
      continue;
    }
    // A state array's elements are read as written, `banned[1]`, a select
    // of it being no element variable of the object.
    std::string_view element_array =
        array != nullptr || rand_queue ? ref.array_name : "";
    ForeachBuild build{
        ForeachInstances(ref, element_array, elems.lo, elems.count, rc),
        ref.body.size(), elems, block.enabled};
    if (!elems.size_var.empty()) {
      for (size_t rel = 0; rel < ref.body.size(); ++rel)
        block.constraints.push_back(SizedForeach(build, rel, rands, rc));
      continue;
    }
    for (const Expr* rel : build.instances) {
      block.constraints.push_back(
          TranslateRelation(rel, rands, rc, /*fold=*/build.fold));
    }
  }
}

}  // namespace delta
