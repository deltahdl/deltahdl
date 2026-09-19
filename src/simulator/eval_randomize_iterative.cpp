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
// `array` from the index `lo`, one instance of each relation of the
// constraint_set per element in index order, built once per class and count
// and kept on the class. A header naming more than one loop variable
// iterates a dimension the object does not model, and instances nothing.
const std::vector<Expr*>& ForeachInstances(const ConstraintForeachRef& ref,
                                           int64_t lo, uint32_t count,
                                           RandomizeCtx& rc) {
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
    ForeachInstance inst{ref.loop_vars[0],
                         ref.array_name,
                         lo + static_cast<int64_t>(i),
                         lo,
                         count,
                         rc};
    for (const Expr* rel : ref.body)
      cached.relations.push_back(Instance(rel, inst));
  }
  return cached.relations;
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
    if (array == nullptr) continue;
    IteratedElements elems = ElementsOf(*array, rands, rc);
    ForeachBuild build{ForeachInstances(ref, elems.lo, elems.count, rc),
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
