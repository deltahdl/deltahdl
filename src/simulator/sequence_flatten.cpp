#include "simulator/sequence_flatten.h"

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// §16.8 lets instances nest, and a cyclic dependency among named sequences is
// an error the elaborator reports; the flattening stops descending here so a
// cycle it is handed all the same ends the instance rather than the run.
constexpr int kMaxInstanceDepth = 16;

using ActualsByFormal = std::unordered_map<std::string_view, Expr*>;

// Whether an actual is the edge-and-signal form ParseSequenceActualArg keeps
// for a formal of type event.
bool IsEventActual(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kUnary &&
         (e->op == TokenKind::kKwPosedge || e->op == TokenKind::kKwNegedge ||
          e->op == TokenKind::kKwEdge);
}

Edge EdgeOfActual(const Expr* e) {
  if (e->op == TokenKind::kKwPosedge) return Edge::kPosedge;
  if (e->op == TokenKind::kKwNegedge) return Edge::kNegedge;
  return Edge::kEdge;
}

// §16.8.1 (c): an actual bound to a formal of a keyword data type is cast to
// that type before it is substituted, so an 8-bit actual passed to a `bit`
// formal is truncated and a `bit` passed to a `byte` formal extended. A `$`,
// an event actual and an untyped formal's actual are substituted as they are.
Expr* CastActual(Expr* actual, TokenKind type_kw, Arena& arena) {
  if (actual == nullptr || type_kw == TokenKind::kEof) return actual;
  if (IsEventActual(actual)) return actual;
  if (actual->kind == ExprKind::kIdentifier && actual->text == "$") {
    return actual;
  }
  std::string_view type_name;
  switch (type_kw) {
    case TokenKind::kKwBit:
      type_name = "bit";
      break;
    case TokenKind::kKwLogic:
      type_name = "logic";
      break;
    case TokenKind::kKwReg:
      type_name = "reg";
      break;
    case TokenKind::kKwByte:
      type_name = "byte";
      break;
    case TokenKind::kKwShortint:
      type_name = "shortint";
      break;
    case TokenKind::kKwInt:
      type_name = "int";
      break;
    case TokenKind::kKwLongint:
      type_name = "longint";
      break;
    case TokenKind::kKwInteger:
      type_name = "integer";
      break;
    default:
      return actual;
  }
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_name;
  cast->range = actual->range;
  cast->lhs = actual;
  return cast;
}

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
// `$` for no upper bound, or the elaboration-time constant §16.8 requires of
// it, evaluated here as a parameter or a literal is. An actual that answers no
// known value leaves the bound as it was, which is the parser's default of 1.
void ResolveDelayBound(uint32_t& bound, std::string_view formal,
                       const ActualsByFormal& actuals, SimContext& ctx,
                       Arena& arena) {
  if (formal.empty()) return;
  auto it = actuals.find(formal);
  if (it == actuals.end() || it->second == nullptr) return;
  const Expr* actual = it->second;
  if (actual->kind == ExprKind::kIdentifier && actual->text == "$") {
    bound = SeqCycleDelay::kUnbounded;
    return;
  }
  Logic4Vec value = EvalExpr(actual, ctx, arena);
  if (!value.IsKnown()) return;
  bound = static_cast<uint32_t>(value.ToUint64());
}

SeqCycleDelay ResolveDelay(SeqCycleDelay delay, const ActualsByFormal& actuals,
                           SimContext& ctx, Arena& arena) {
  ResolveDelayBound(delay.min, delay.min_formal, actuals, ctx, arena);
  ResolveDelayBound(delay.max, delay.max_formal, actuals, ctx, arena);
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
// which the parser keeps after the positional ones with their names beside,
// each cast as §16.8.1 has it for the formal's type.
ActualsByFormal BindActuals(const ModuleItem* decl, const Expr* instance,
                            Arena& arena) {
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
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_type_kw.size();
       ++i) {
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end()) continue;
    it->second = CastActual(it->second, decl->prop_formal_type_kw[i], arena);
  }
  return actuals;
}

// §16.8.1 (b): the instantiated sequence's clock with its formals replaced by
// the actuals: an event actual supplies the edge and the signal, an ordinary
// actual the signal alone under the edge the clock wrote.
std::vector<EventExpr> SubstituteClock(const std::vector<EventExpr>& clock,
                                       const ActualsByFormal& actuals,
                                       Arena& arena) {
  std::vector<EventExpr> out;
  for (const EventExpr& ev : clock) {
    EventExpr copy = ev;
    if (ev.signal != nullptr && ev.signal->kind == ExprKind::kIdentifier) {
      auto it = actuals.find(ev.signal->text);
      if (it != actuals.end() && IsEventActual(it->second)) {
        copy.edge = EdgeOfActual(it->second);
        copy.signal = it->second->lhs;
        out.push_back(copy);
        continue;
      }
      // A signal under an edge is watched as the object it names, so the cast
      // §16.8.1 (c) put on the actual of a typed formal is looked through.
      if (it != actuals.end() && it->second != nullptr &&
          it->second->kind == ExprKind::kCast) {
        copy.signal = it->second->lhs;
        copy.iff_condition =
            SubstituteFormals(ev.iff_condition, actuals, arena);
        out.push_back(copy);
        continue;
      }
    }
    copy.signal = SubstituteFormals(ev.signal, actuals, arena);
    copy.iff_condition = SubstituteFormals(ev.iff_condition, actuals, arena);
    out.push_back(copy);
  }
  return out;
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
             LinearSequence& out, int depth);

// An operand of the sequence being flattened that instantiates a named
// sequence: the declaration instantiated, the instance as written, and the
// delay written before it.
struct InstanceOperand {
  const ModuleItem* inner;
  const Expr* instance;
  SeqCycleDelay before;
};

// Appends the instantiated body's flattened operands with the actuals
// substituted, its clock taken where the outer sequence has none.
bool ExpandInstance(const InstanceOperand& op, SimContext& ctx, Arena& arena,
                    LinearSequence& out, int depth) {
  LinearSequence body;
  if (!Flatten(op.inner, ctx, arena, body, depth + 1)) return false;
  ActualsByFormal actuals = BindActuals(op.inner, op.instance, arena);
  if (out.clock.empty() && !body.clock.empty()) {
    out.clock = SubstituteClock(body.clock, actuals, arena);
  }
  for (size_t j = 0; j < body.operands.size(); ++j) {
    out.operands.push_back(SubstituteFormals(body.operands[j], actuals, arena));
    SeqCycleDelay delay = ResolveDelay(body.delays[j], actuals, ctx, arena);
    out.delays.push_back(j == 0 ? AddDelays(op.before, delay) : delay);
  }
  return true;
}

bool Flatten(const ModuleItem* seq, SimContext& ctx, Arena& arena,
             LinearSequence& out, int depth) {
  if (seq == nullptr || seq->seq_linear_operands.empty()) return false;
  if (depth > kMaxInstanceDepth) return false;
  out.clock = seq->seq_clock;
  for (size_t i = 0; i < seq->seq_linear_operands.size(); ++i) {
    Expr* operand = seq->seq_linear_operands[i];
    const SeqCycleDelay& before = seq->seq_linear_delays[i];
    const ModuleItem* inner = InstantiatedSequence(operand, ctx);
    if (inner == nullptr) {
      out.operands.push_back(operand);
      out.delays.push_back(before);
    } else if (!ExpandInstance({inner, operand, before}, ctx, arena, out,
                               depth)) {
      return false;
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
