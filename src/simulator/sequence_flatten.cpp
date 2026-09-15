#include "simulator/sequence_flatten.h"

#include <cstddef>
#include <cstdint>
#include <string>
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

// §16.10 over the match items of one operand: the right-hand sides read the
// actuals as the operands do, and an assigned local named after a formal --
// a local variable formal argument, whose flattened name the actual is -- is
// renamed with it.
std::vector<SeqMatchAssign> SubstituteMatchItems(
    const std::vector<SeqMatchAssign>& items, const ActualsByFormal& actuals,
    Arena& arena) {
  std::vector<SeqMatchAssign> out;
  for (const SeqMatchAssign& item : items) {
    SeqMatchAssign copy = item;
    auto it = actuals.find(item.lvar);
    if (it != actuals.end() && it->second != nullptr &&
        it->second->kind == ExprKind::kIdentifier) {
      copy.lvar = it->second->text;
    }
    copy.rhs = SubstituteFormals(item.rhs, actuals, arena);
    out.push_back(copy);
  }
  return out;
}

// An identifier expression naming `name`, arena-owned, for a local of an
// instantiated body renamed into the flattened sequence.
Expr* LocalNameExpr(std::string_view name, Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

std::string_view RenamedLocal(std::string_view name, int instance,
                              Arena& arena) {
  std::string renamed = std::string(name) + "@" + std::to_string(instance);
  return {arena.AllocString(renamed.data(), renamed.size()), renamed.size()};
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

// §16.8.2: the local variable formal arguments of `decl`, each with its
// direction, in the order of the formals. The directions the port scan keeps
// stand in the order of the local formals alone.
struct LocalFormal {
  size_t index;
  Direction direction;
};

std::vector<LocalFormal> LocalFormalsOf(const ModuleItem* decl) {
  std::vector<LocalFormal> out;
  size_t local_index = 0;
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    bool is_local =
        i < decl->prop_formal_is_local.size() && decl->prop_formal_is_local[i];
    if (!is_local) continue;
    Direction dir = local_index < decl->prop_seq_local_lvar_directions.size()
                        ? decl->prop_seq_local_lvar_directions[local_index]
                        : Direction::kInput;
    out.push_back({i, dir});
    ++local_index;
  }
  return out;
}

// §16.8.2 and §16.10: every local of the instantiated body -- the ones it
// declares and its local variable formal arguments -- becomes a local of the
// flattened sequence under a name of its own, `name@N` for the Nth instance,
// and the body's references to it are renamed through the actuals map. A
// local formal's actual is set aside before the renaming overwrites its entry,
// since the initialization and the assignment back are written over it.
struct LocalBinding {
  std::string_view renamed;
  Expr* actual;
  Direction direction;
};

std::vector<LocalBinding> RenameInstanceLocals(
    const ModuleItem* inner, const LinearSequence& body, int instance,
    ActualsByFormal& actuals, LinearSequence& out, Arena& arena) {
  std::vector<LocalBinding> formals;
  for (const LocalFormal& lf : LocalFormalsOf(inner)) {
    std::string_view name = inner->prop_formals[lf.index];
    LocalBinding binding;
    binding.renamed = RenamedLocal(name, instance, arena);
    auto it = actuals.find(name);
    binding.actual = it == actuals.end() ? nullptr : it->second;
    binding.direction = lf.direction;
    formals.push_back(binding);
    SeqLocalDecl decl;
    decl.name = binding.renamed;
    decl.type_kw = lf.index < inner->prop_formal_type_kw.size()
                       ? inner->prop_formal_type_kw[lf.index]
                       : TokenKind::kKwInt;
    out.locals.push_back(decl);
    actuals[name] = LocalNameExpr(binding.renamed, arena);
  }
  for (const SeqLocalDecl& local : body.locals) {
    SeqLocalDecl decl = local;
    decl.name = RenamedLocal(local.name, instance, arena);
    decl.init = SubstituteFormals(local.init, actuals, arena);
    out.locals.push_back(decl);
    actuals[local.name] = LocalNameExpr(decl.name, arena);
  }
  return formals;
}

// Appends the instantiated body's flattened operands with the actuals
// substituted, its clock taken where the outer sequence has none, and the
// §16.8.2 assignments of its local variable formal arguments: the
// initialization from the actual before the first operand, and the assignment
// back to the actual's local at the last operand's match.
bool ExpandInstance(const InstanceOperand& op, SimContext& ctx, Arena& arena,
                    LinearSequence& out, int depth) {
  LinearSequence body;
  if (!Flatten(op.inner, ctx, arena, body, depth + 1)) return false;
  ActualsByFormal actuals = BindActuals(op.inner, op.instance, arena);
  // The operands already flattened number the instance, each instance adding
  // at least one, so the locals of two instances of one sequence differ.
  int instance = static_cast<int>(out.operands.size()) + 1;
  std::vector<LocalBinding> formals =
      RenameInstanceLocals(op.inner, body, instance, actuals, out, arena);
  if (out.clock.empty() && !body.clock.empty()) {
    out.clock = SubstituteClock(body.clock, actuals, arena);
  }
  size_t first = out.operands.size();
  for (size_t j = 0; j < body.operands.size(); ++j) {
    out.operands.push_back(SubstituteFormals(body.operands[j], actuals, arena));
    SeqCycleDelay delay = ResolveDelay(body.delays[j], actuals, ctx, arena);
    out.delays.push_back(j == 0 ? AddDelays(op.before, delay) : delay);
    out.match_items.push_back(
        SubstituteMatchItems(body.match_items[j], actuals, arena));
  }
  if (out.operands.size() == first) return true;
  std::vector<SeqMatchAssign>& at_first = out.match_items[first];
  std::vector<SeqMatchAssign>& at_last = out.match_items.back();
  for (const LocalBinding& f : formals) {
    if (f.actual == nullptr) continue;
    if (f.direction != Direction::kOutput) {
      SeqMatchAssign init;
      init.lvar = f.renamed;
      init.rhs = f.actual;
      init.init = true;
      at_first.insert(at_first.begin(), init);
    }
    if (f.direction != Direction::kInput &&
        f.actual->kind == ExprKind::kIdentifier) {
      SeqMatchAssign back;
      back.lvar = f.actual->text;
      back.rhs = LocalNameExpr(f.renamed, arena);
      at_last.push_back(back);
    }
  }
  return true;
}

bool Flatten(const ModuleItem* seq, SimContext& ctx, Arena& arena,
             LinearSequence& out, int depth) {
  if (seq == nullptr || seq->seq_linear.operands.empty()) return false;
  if (depth > kMaxInstanceDepth) return false;
  out.clock = seq->seq_clock;
  out.locals = seq->seq_linear.locals;
  const SeqLinearBody& body = seq->seq_linear;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    Expr* operand = body.operands[i];
    const SeqCycleDelay& before = body.delays[i];
    const ModuleItem* inner = InstantiatedSequence(operand, ctx);
    if (inner == nullptr) {
      out.operands.push_back(operand);
      out.delays.push_back(before);
      out.match_items.push_back(body.match_items[i]);
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
