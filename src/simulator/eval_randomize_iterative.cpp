#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"

namespace delta {

// 18.5.7: iterative constraints, which constrain an arrayed variable through
// a loop variable and an indexing expression -- a foreach iterative constraint
// (18.5.7.1) -- or through an array reduction method (18.5.7.2).

namespace {

// The substitution one instance of a foreach constraint_set makes: the loop
// variable stands for `index`, and a select of `array` at the loop variable
// names the element at that index.
struct ForeachInstance {
  std::string_view loop_var;
  std::string_view array;
  int64_t index;
};

Expr* Instance(const Expr* e, const ForeachInstance& inst, Arena& arena);

// An identifier node spelling `text`, the text held by the arena.
Expr* Identifier(std::string_view text, const Expr* like, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->range = like->range;
  id->text = {arena.AllocString(text.data(), text.size()), text.size()};
  return id;
}

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

// Whether `e` is a select of the iterated array at the loop variable alone,
// `A[i]`, which one instance reads as the element's own variable.
bool SelectsElement(const Expr* e, const ForeachInstance& inst) {
  return e->kind == ExprKind::kSelect && e->index_end == nullptr &&
         e->base != nullptr && e->base->kind == ExprKind::kIdentifier &&
         e->base->text == inst.array && e->index != nullptr &&
         e->index->kind == ExprKind::kIdentifier &&
         e->index->text == inst.loop_var;
}

// A copy of `e` whose subexpressions are instanced.
Expr* CopyInstanced(const Expr* e, const ForeachInstance& inst, Arena& arena) {
  auto* copy = arena.Create<Expr>(*e);
  copy->lhs = Instance(e->lhs, inst, arena);
  copy->rhs = Instance(e->rhs, inst, arena);
  copy->condition = Instance(e->condition, inst, arena);
  copy->true_expr = Instance(e->true_expr, inst, arena);
  copy->false_expr = Instance(e->false_expr, inst, arena);
  copy->base = Instance(e->base, inst, arena);
  copy->index = Instance(e->index, inst, arena);
  copy->index_end = Instance(e->index_end, inst, arena);
  copy->with_expr = Instance(e->with_expr, inst, arena);
  copy->repeat_count = Instance(e->repeat_count, inst, arena);
  for (auto*& arg : copy->args) arg = Instance(arg, inst, arena);
  for (auto*& elem : copy->elements) elem = Instance(elem, inst, arena);
  for (auto*& key : copy->pattern_keys) key = Instance(key, inst, arena);
  return copy;
}

// 18.5.7.1: `e` as one instance of the constraint_set reads it: the loop
// variable as the index, a select of the array at the loop variable as the
// element's variable, and anything else as written over instanced operands.
// A select of the array at another index is left as the select it is, which
// the trial reads against the elements it binds.
Expr* Instance(const Expr* e, const ForeachInstance& inst, Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier && e->text == inst.loop_var)
    return IndexLiteral(inst.index, e, arena);
  if (SelectsElement(e, inst))
    return Identifier(ClassArrayElementKey(inst.array, inst.index), e, arena);
  return CopyInstanced(e, inst, arena);
}

// 18.5.7.1: the relations `ref` instances over the array `array`, built once
// per class and kept on it. A header naming more than one loop variable
// iterates a dimension the object does not model, and instances nothing.
const std::vector<Expr*>& ForeachInstances(
    const ConstraintForeachRef& ref, const ClassTypeInfo::PropertyInfo& array,
    RandomizeCtx& rc) {
  auto& cache = rc.obj->type->foreach_instances;
  auto it = cache.find(&ref);
  if (it != cache.end()) return it->second;
  std::vector<Expr*>& instances = cache[&ref];
  if (ref.loop_vars.size() != 1 || ref.loop_vars[0].empty()) return instances;
  for (uint32_t i = 0; i < array.array_size; ++i) {
    ForeachInstance inst{ref.loop_vars[0], ref.array_name,
                         array.array_lo + static_cast<int64_t>(i)};
    for (const Expr* rel : ref.body)
      instances.push_back(Instance(rel, inst, rc.arena));
  }
  return instances;
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
    if (ri.array_base == array) names.push_back(ri.name);
  }
  return names;
}

// 18.5.7.2: `e` as a reduction method called with no argument and no with
// clause on a rand array member, filling the method's operand and the
// element variables; false for any other expression.
bool ReductionCall(const Expr* e, std::vector<RandInfo>& rands,
                   ArrayReductionOp& op, std::vector<std::string>& elements) {
  if (e == nullptr || e->kind != ExprKind::kCall || !e->args.empty() ||
      e->with_expr != nullptr || e->lhs == nullptr ||
      e->lhs->kind != ExprKind::kMemberAccess || e->lhs->is_scope_resolution ||
      e->lhs->lhs == nullptr || e->lhs->rhs == nullptr ||
      e->lhs->lhs->kind != ExprKind::kIdentifier ||
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
  // 18.5.7.2: the result is of the element type, so the fold is held to the
  // element's width.
  const RandInfo* elem = FindRand(rands, elements.front());
  out.reduce_width = elem != nullptr ? elem->var.width : 32;
  out.reduce_vars = elements;
  out.ref_vars = std::move(elements);
  return true;
}

void AddForeachConstraints(const ClassMember* m, std::vector<RandInfo>& rands,
                           RandomizeCtx& rc, ConstraintBlock& block) {
  for (const auto& ref : m->constraint_foreach_refs) {
    if (ref.body.empty()) continue;
    const auto* array = FindClassArrayProperty(rc.obj->type, ref.array_name);
    if (array == nullptr) continue;
    for (const Expr* rel : ForeachInstances(ref, *array, rc)) {
      block.constraints.push_back(
          TranslateRelation(rel, rands, rc, /*fold=*/block.enabled));
    }
  }
}

}  // namespace delta
