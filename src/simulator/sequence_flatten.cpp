#include "simulator/sequence_flatten.h"

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// §16.8 lets instances nest, and a cyclic dependency among named sequences is
// an error the elaborator reports; the flattening stops descending here so a
// cycle it is handed all the same ends the instance rather than the run.
constexpr int kMaxInstanceDepth = 16;

using ActualsByFormal = std::unordered_map<std::string_view, Expr*>;

// Annex F.4.1's substitution over one expression: a copy of `e` in which every
// identifier naming a formal is replaced by the actual bound to it. The actual
// is shared rather than copied, so an actual that is an expression stands as
// one term, which is what the clause's parenthesising of the actual secures.
Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) {
    auto it = actuals.find(e->text);
    if (it != actuals.end()) return it->second;
  }
  auto* copy = arena.Create<Expr>(*e);
  copy->lhs = SubstituteFormals(e->lhs, actuals, arena);
  copy->rhs = SubstituteFormals(e->rhs, actuals, arena);
  copy->condition = SubstituteFormals(e->condition, actuals, arena);
  copy->true_expr = SubstituteFormals(e->true_expr, actuals, arena);
  copy->false_expr = SubstituteFormals(e->false_expr, actuals, arena);
  copy->base = SubstituteFormals(e->base, actuals, arena);
  copy->index = SubstituteFormals(e->index, actuals, arena);
  copy->index_end = SubstituteFormals(e->index_end, actuals, arena);
  copy->with_expr = SubstituteFormals(e->with_expr, actuals, arena);
  copy->repeat_count = SubstituteFormals(e->repeat_count, actuals, arena);
  for (auto& sub : copy->elements) sub = SubstituteFormals(sub, actuals, arena);
  for (auto& sub : copy->args) sub = SubstituteFormals(sub, actuals, arena);
  return copy;
}

// The value a delay bound written as a formal's name takes from its actual:
// an integer literal, or `$` for no upper bound. Any other actual leaves the
// bound as it was, which is the parser's default of 1.
void ResolveDelayBound(uint32_t& bound, std::string_view formal,
                       const ActualsByFormal& actuals) {
  if (formal.empty()) return;
  auto it = actuals.find(formal);
  if (it == actuals.end() || it->second == nullptr) return;
  const Expr* actual = it->second;
  if (actual->kind == ExprKind::kIdentifier && actual->text == "$") {
    bound = SeqCycleDelay::kUnbounded;
    return;
  }
  if (actual->kind != ExprKind::kIntegerLiteral) return;
  uint32_t value = 0;
  for (char c : actual->text) {
    if (c == '_') continue;
    if (c < '0' || c > '9') break;
    value = value * 10 + static_cast<uint32_t>(c - '0');
  }
  bound = value;
}

SeqCycleDelay ResolveDelay(SeqCycleDelay delay,
                           const ActualsByFormal& actuals) {
  ResolveDelayBound(delay.min, delay.min_formal, actuals);
  ResolveDelayBound(delay.max, delay.max_formal, actuals);
  delay.min_formal = {};
  delay.max_formal = {};
  return delay;
}

// §16.7: `##a` before an instance whose body opens with `##b` is a delay of
// a + b to the body's first operand, unbounded where either is.
SeqCycleDelay AddDelays(const SeqCycleDelay& before,
                        const SeqCycleDelay& lead) {
  SeqCycleDelay sum;
  sum.min = before.min + lead.min;
  bool unbounded = before.max == SeqCycleDelay::kUnbounded ||
                   lead.max == SeqCycleDelay::kUnbounded;
  sum.max = unbounded ? SeqCycleDelay::kUnbounded : before.max + lead.max;
  return sum;
}

// §16.8: the actuals of an instance bound to the declaration's formals, by
// position for the leading actuals and by name for the `.formal(actual)` ones,
// which the parser keeps after the positional ones with their names beside.
ActualsByFormal BindActuals(const ModuleItem* decl, const Expr* instance) {
  ActualsByFormal actuals;
  if (instance->kind != ExprKind::kCall) return actuals;
  size_t named = instance->arg_names.size();
  size_t positional = instance->args.size() - named;
  for (size_t i = 0; i < positional && i < decl->prop_formals.size(); ++i) {
    actuals[decl->prop_formals[i]] = instance->args[i];
  }
  for (size_t i = 0; i < named; ++i) {
    actuals[instance->arg_names[i]] = instance->args[positional + i];
  }
  return actuals;
}

const ModuleItem* InstantiatedSequence(const Expr* operand, SimContext& ctx) {
  if (operand == nullptr) return nullptr;
  if (operand->kind != ExprKind::kIdentifier &&
      operand->kind != ExprKind::kCall) {
    return nullptr;
  }
  std::string_view name =
      operand->kind == ExprKind::kCall ? operand->callee : operand->text;
  return ctx.FindSequenceDecl(name);
}

bool Flatten(const ModuleItem* seq, SimContext& ctx, Arena& arena,
             LinearSequence& out, int depth) {
  if (seq == nullptr || seq->seq_linear_operands.empty()) return false;
  if (depth > kMaxInstanceDepth) return false;
  for (size_t i = 0; i < seq->seq_linear_operands.size(); ++i) {
    Expr* operand = seq->seq_linear_operands[i];
    const SeqCycleDelay& before = seq->seq_linear_delays[i];
    const ModuleItem* inner = InstantiatedSequence(operand, ctx);
    if (inner == nullptr) {
      out.operands.push_back(operand);
      out.delays.push_back(before);
      continue;
    }
    LinearSequence body;
    if (!Flatten(inner, ctx, arena, body, depth + 1)) return false;
    ActualsByFormal actuals = BindActuals(inner, operand);
    for (size_t j = 0; j < body.operands.size(); ++j) {
      out.operands.push_back(
          SubstituteFormals(body.operands[j], actuals, arena));
      SeqCycleDelay delay = ResolveDelay(body.delays[j], actuals);
      out.delays.push_back(j == 0 ? AddDelays(before, delay) : delay);
    }
  }
  return true;
}

}  // namespace

bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out) {
  out = LinearSequence{};
  return Flatten(seq, ctx, arena, out, 0);
}

}  // namespace delta
