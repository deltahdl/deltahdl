#include "simulator/sequence_flatten.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// §16.8 lets instances nest, and a cyclic dependency among named sequences is
// an error the elaborator reports; the flattening stops descending here so a
// cycle it is handed all the same ends the instance rather than the run.
constexpr int kMaxInstanceDepth = 16;

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

// §16.10 over the match items of one operand: the right-hand sides read the
// actuals as the operands do, and an assigned local named after a formal --
// a local variable formal argument, whose flattened name the actual is -- is
// renamed with it. A local of a named property, or a local variable formal
// argument of one, stands as the literal of the attempt's copy of it
// (§16.13.7, §16.12.19), which the item then assigns.
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
    } else if (it != actuals.end() && it->second != nullptr &&
               it->second->kind == ExprKind::kIntegerLiteral) {
      copy.local_copy = it->second;
    }
    copy.rhs = SubstituteFormals(item.rhs, actuals, arena);
    if (item.call != nullptr) {
      copy.call = SubstituteFormals(item.call, actuals, arena);
    }
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

}  // namespace

// The parser keeps the named actuals after the positional ones with their
// names beside.
ActualsByFormal BindInstanceActuals(const ModuleItem* decl,
                                    const Expr* instance, Arena& arena) {
  ActualsByFormal actuals = BindActuals(decl->prop_formals, instance);
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_type_kw.size();
       ++i) {
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end()) continue;
    it->second = CastActual(it->second, decl->prop_formal_type_kw[i], arena);
  }
  return actuals;
}

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

namespace {

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
  SeqRepetition repetition;
  std::vector<EventExpr> clock;
};

// §16.13.1: the clock of the operand just appended to `out`, kept parallel
// to the operands once any operand names one.
void PushOperandClock(LinearSequence& out,
                      const std::vector<EventExpr>& clock) {
  if (clock.empty() && out.operand_clocks.empty()) return;
  while (out.operand_clocks.size() + 1 < out.operands.size()) {
    out.operand_clocks.emplace_back();
  }
  out.operand_clocks.push_back(clock);
}

const std::vector<EventExpr>& BodyOperandClock(const SeqLinearBody& body,
                                               size_t pos) {
  static const std::vector<EventExpr> kNone;
  return pos < body.clocks.size() ? body.clocks[pos] : kNone;
}

// §16.9.2: consecutive repetition of an instance by an exact count, unrolled
// as the parser unrolls a group's, the operands from `first` on appended
// again `count - 1` times with the copy's first operand a tick after the
// last. A range or an unbounded count on an instance is not read.
bool UnrollInstanceRepetition(LinearSequence& out, size_t first,
                              const SeqRepetition& rep) {
  if (rep.kind == SeqRepetition::Kind::kNone) return true;
  if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
  if (rep.min != rep.max || rep.min == 0) return false;
  size_t n = out.operands.size() - first;
  for (uint32_t k = 1; k < rep.min; ++k) {
    for (size_t i = 0; i < n; ++i) {
      out.operands.push_back(out.operands[first + i]);
      SeqCycleDelay delay = out.delays[first + i];
      if (i == 0) {
        delay.min = 1;
        delay.max = 1;
      }
      out.delays.push_back(delay);
      out.match_items.push_back(out.match_items[first + i]);
      out.repetitions.push_back(out.repetitions[first + i]);
      PushOperandClock(out, OperandClock(out, first + i));
    }
  }
  return true;
}

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

// Where the locals of one instance are renamed into: the number the instance
// takes in the flattened sequence, that sequence, and the arena the new names
// live in.
struct Renaming {
  int instance;
  LinearSequence& out;
  Arena& arena;
};

// One local variable formal argument of `inner` renamed into the flattened
// sequence, its actual recorded before the renaming replaces it in `actuals`.
LocalBinding RenameLocalFormal(const ModuleItem* inner, const LocalFormal& lf,
                               ActualsByFormal& actuals, Renaming& renaming) {
  std::string_view name = inner->prop_formals[lf.index];
  LocalBinding binding;
  binding.renamed = RenamedLocal(name, renaming.instance, renaming.arena);
  auto it = actuals.find(name);
  binding.actual = it == actuals.end() ? nullptr : it->second;
  binding.direction = lf.direction;
  SeqLocalDecl decl;
  decl.name = binding.renamed;
  decl.type_kw = lf.index < inner->prop_formal_type_kw.size()
                     ? inner->prop_formal_type_kw[lf.index]
                     : TokenKind::kKwInt;
  renaming.out.locals.push_back(decl);
  actuals[name] = LocalNameExpr(binding.renamed, renaming.arena);
  return binding;
}

std::vector<LocalBinding> RenameInstanceLocals(const ModuleItem* inner,
                                               const LinearSequence& body,
                                               ActualsByFormal& actuals,
                                               Renaming& renaming) {
  std::vector<LocalBinding> formals;
  for (const LocalFormal& lf : LocalFormalsOf(inner)) {
    formals.push_back(RenameLocalFormal(inner, lf, actuals, renaming));
  }
  for (const SeqLocalDecl& local : body.locals) {
    SeqLocalDecl decl = local;
    decl.name = RenamedLocal(local.name, renaming.instance, renaming.arena);
    decl.init = SubstituteFormals(local.init, actuals, renaming.arena);
    renaming.out.locals.push_back(decl);
    actuals[local.name] = LocalNameExpr(decl.name, renaming.arena);
  }
  return formals;
}

// §16.8.2: the assignments an instance owes for its local variable formal
// arguments, written as match items: the initialization of an input or inout
// one from its actual before the instance's first operand, and the assignment
// of an inout or output one back to the actual's local variable at the
// instance's last operand. The actual of an inout or output formal is a
// reference to a local variable, which the cast §16.8.1 put on it is looked
// through to name.
void AddLocalFormalAssignments(const std::vector<LocalBinding>& formals,
                               std::vector<SeqMatchAssign>& at_first,
                               std::vector<SeqMatchAssign>& at_last,
                               Arena& arena) {
  for (const LocalBinding& f : formals) {
    if (f.actual == nullptr) continue;
    if (f.direction != Direction::kOutput) {
      SeqMatchAssign init;
      init.lvar = f.renamed;
      init.rhs = f.actual;
      init.init = true;
      at_first.insert(at_first.begin(), init);
    }
    const Expr* target = f.actual;
    if (target->kind == ExprKind::kCast && target->lhs != nullptr) {
      target = target->lhs;
    }
    if (f.direction != Direction::kInput &&
        target->kind == ExprKind::kIdentifier) {
      SeqMatchAssign back;
      back.lvar = target->text;
      back.rhs = LocalNameExpr(f.renamed, arena);
      at_last.push_back(back);
    }
  }
}

// §16.13.1 and §16.13.3: the clock the operand at `j` of an instantiated
// body is evaluated on: the one it names, else the one the declaration is
// declared with, its formals replaced by the actuals, else the one flowing
// into the instance.
std::vector<EventExpr> InstanceOperandClock(const LinearSequence& body,
                                            size_t j, const InstanceOperand& op,
                                            const ActualsByFormal& actuals,
                                            Arena& arena) {
  const std::vector<EventExpr>& own = OperandClock(body, j);
  if (!own.empty()) return own;
  if (!body.declared_clock.empty()) {
    return SubstituteClock(body.declared_clock, actuals, arena);
  }
  return op.clock;
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
  // A sequence with `intersect`, `and` or `or` operands of its own does not
  // splice into one chain.
  if (!body.alternatives.empty() || !body.conjuncts.empty() ||
      !body.intersects.empty()) {
    return false;
  }
  ActualsByFormal actuals = BindInstanceActuals(op.inner, op.instance, arena);
  // The operands already flattened number the instance, each instance adding
  // at least one, so the locals of two instances of one sequence differ.
  Renaming renaming{static_cast<int>(out.operands.size()) + 1, out, arena};
  std::vector<LocalBinding> formals =
      RenameInstanceLocals(op.inner, body, actuals, renaming);
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
    out.repetitions.push_back(body.repetitions[j]);
    // §16.13.1 and §16.13.3: an operand of the instantiated body is
    // evaluated on the clock it names, else on the declaration's own, else
    // on the one flowing into the instance.
    PushOperandClock(out, InstanceOperandClock(body, j, op, actuals, arena));
  }
  // §16.9.9: a throughout of the instantiated body spans the same operands
  // where they now stand, its condition over the actuals.
  for (SeqThroughout guard : body.throughouts) {
    guard.cond = SubstituteFormals(guard.cond, actuals, arena);
    guard.first += first;
    guard.last += first;
    out.throughouts.push_back(guard);
  }
  if (out.operands.size() == first) return true;
  AddLocalFormalAssignments(formals, out.match_items[first],
                            out.match_items.back(), arena);
  return UnrollInstanceRepetition(out, first, op.repetition);
}

bool FlattenChain(const SeqLinearBody& body, SimContext& ctx, Arena& arena,
                  LinearSequence& out, int depth);

// One `intersect` operand with its intersects, each flattened as a chain of
// its own; an instance in any that names the clock gives it to the whole.
bool FlattenIntersection(const SeqLinearBody& body, SimContext& ctx,
                         Arena& arena, LinearSequence& out, int depth) {
  if (!FlattenChain(body, ctx, arena, out, depth)) return false;
  for (const SeqLinearBody& operand : body.intersects) {
    LinearSequence flat;
    flat.clock = out.clock;
    if (!FlattenChain(operand, ctx, arena, flat, depth)) return false;
    if (out.clock.empty()) out.clock = flat.clock;
    out.intersects.push_back(std::move(flat));
  }
  return true;
}

// One `and` operand with its conjuncts, each flattened as an intersection of
// its own; an instance in any that names the clock gives it to the whole.
bool FlattenConjunction(const SeqLinearBody& body, SimContext& ctx,
                        Arena& arena, LinearSequence& out, int depth) {
  if (!FlattenIntersection(body, ctx, arena, out, depth)) return false;
  for (const SeqLinearBody& conjunct : body.conjuncts) {
    LinearSequence flat;
    flat.clock = out.clock;
    if (!FlattenIntersection(conjunct, ctx, arena, flat, depth)) return false;
    if (out.clock.empty()) out.clock = flat.clock;
    out.conjuncts.push_back(std::move(flat));
  }
  return true;
}

// §16.9.8: the match items written on a `first_match` are the operand's own,
// so they are executed at the end of each `or` operand's chain.
void AttachFirstMatchItems(const SeqLinearBody& body, LinearSequence& out) {
  if (body.first_match_items.empty()) return;
  for (const SeqMatchAssign& item : body.first_match_items) {
    out.match_items.back().push_back(item);
    for (LinearSequence& alt : out.alternatives) {
      alt.match_items.back().push_back(item);
    }
  }
}

// Whether the body is one instance of a named sequence, written with no
// arguments, delay, repetition, match items or operator of its own: such a
// body stands for the instantiated sequence whole, `or` operands and all,
// where an instance among other operands splices into one chain.
const ModuleItem* BareInstance(const SeqLinearBody& body, SimContext& ctx) {
  if (body.operands.size() != 1 || !body.alternatives.empty() ||
      !body.conjuncts.empty() || !body.intersects.empty()) {
    return nullptr;
  }
  const Expr* operand = body.operands[0];
  if (operand->kind != ExprKind::kIdentifier) return nullptr;
  if (body.delays[0].min != 0 || body.delays[0].max != 0) return nullptr;
  if (!body.match_items[0].empty()) return nullptr;
  if (body.repetitions[0].kind != SeqRepetition::Kind::kNone) return nullptr;
  return InstantiatedSequence(operand, ctx);
}

// A body that is one bare instance stands for the instantiated sequence
// whole, under the body's own clock where it has one, the instantiated
// sequence's otherwise.
bool FlattenBareInstance(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                         LinearSequence& out, int depth) {
  const ModuleItem* inner = BareInstance(seq->seq_linear, ctx);
  if (!Flatten(inner, ctx, arena, out, depth + 1)) return false;
  if (!seq->seq_clock.empty()) {
    out.clock = seq->seq_clock;
    out.declared_clock = seq->seq_clock;
  }
  out.first_match = out.first_match || seq->seq_linear.first_match;
  AttachFirstMatchItems(seq->seq_linear, out);
  return true;
}

bool Flatten(const ModuleItem* seq, SimContext& ctx, Arena& arena,
             LinearSequence& out, int depth) {
  if (seq == nullptr || seq->seq_linear.operands.empty()) return false;
  if (depth > kMaxInstanceDepth) return false;
  const SeqLinearBody& body = seq->seq_linear;
  if (BareInstance(body, ctx) != nullptr) {
    return FlattenBareInstance(seq, ctx, arena, out, depth);
  }
  out.clock = seq->seq_clock;
  out.declared_clock = seq->seq_clock;
  out.clock_out = body.clock_out;
  out.first_match = body.first_match;
  if (!FlattenConjunction(body, ctx, arena, out, depth)) return false;
  // §16.9.7: each `or` operand is flattened on its own.
  for (const SeqLinearBody& alt : body.alternatives) {
    LinearSequence flat;
    flat.clock = out.clock;
    if (!FlattenConjunction(alt, ctx, arena, flat, depth)) return false;
    if (out.clock.empty()) out.clock = flat.clock;
    out.alternatives.push_back(std::move(flat));
  }
  AttachFirstMatchItems(body, out);
  return true;
}

// One chain of a body: its operands, an instance among them expanded, with
// the chain's locals.
bool FlattenChain(const SeqLinearBody& body, SimContext& ctx, Arena& arena,
                  LinearSequence& out, int depth) {
  out.locals = body.locals;
  // Where each of the body's operands begins and ends among the flattened
  // ones, an instance among them expanding to several.
  std::vector<size_t> begins;
  std::vector<size_t> ends;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    Expr* operand = body.operands[i];
    const SeqCycleDelay& before = body.delays[i];
    const ModuleItem* inner = InstantiatedSequence(operand, ctx);
    begins.push_back(out.operands.size());
    if (inner == nullptr) {
      out.operands.push_back(operand);
      out.delays.push_back(before);
      out.match_items.push_back(body.match_items[i]);
      out.repetitions.push_back(body.repetitions[i]);
      PushOperandClock(out, BodyOperandClock(body, i));
    } else if (!ExpandInstance({inner, operand, before, body.repetitions[i],
                                BodyOperandClock(body, i)},
                               ctx, arena, out, depth)) {
      return false;
    }
    ends.push_back(out.operands.size() - 1);
  }
  // §16.9.9: a throughout spans the flattened operands its operands became.
  for (SeqThroughout guard : body.throughouts) {
    guard.first = begins[guard.first];
    guard.last = ends[guard.last];
    out.throughouts.push_back(guard);
  }
  return true;
}

}  // namespace

void ForEachLinearSequenceExpr(const LinearSequence& body,
                               const std::function<void(const Expr*)>& fn) {
  for (const Expr* operand : body.operands) fn(operand);
  for (const auto& items : body.match_items) {
    for (const SeqMatchAssign& item : items) {
      if (item.rhs != nullptr) fn(item.rhs);
      if (item.call != nullptr) fn(item.call);
    }
  }
  for (const SeqThroughout& guard : body.throughouts) fn(guard.cond);
  for (const LinearSequence& inner : body.intersects) {
    ForEachLinearSequenceExpr(inner, fn);
  }
  for (const LinearSequence& inner : body.conjuncts) {
    ForEachLinearSequenceExpr(inner, fn);
  }
  for (const LinearSequence& inner : body.alternatives) {
    ForEachLinearSequenceExpr(inner, fn);
  }
}

const std::vector<EventExpr>& OperandClock(const LinearSequence& body,
                                           size_t pos) {
  static const std::vector<EventExpr> kNone;
  return pos < body.operand_clocks.size() ? body.operand_clocks[pos] : kNone;
}

bool NamesAnotherClock(const LinearSequence& body) {
  for (const auto& clock : body.operand_clocks) {
    if (clock.empty()) continue;
    if (clock.size() != body.clock.size()) return true;
    for (size_t i = 0; i < clock.size(); ++i) {
      const EventExpr& a = clock[i];
      const EventExpr& b = body.clock[i];
      if (a.edge != b.edge || a.signal == nullptr || b.signal == nullptr ||
          a.signal->text != b.signal->text) {
        return true;
      }
    }
  }
  return false;
}

int OperandClockIndex(const LinearSequence& body, size_t pos) {
  return pos < body.operand_clock_index.size() ? body.operand_clock_index[pos]
                                               : 0;
}

bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out) {
  out = LinearSequence{};
  return Flatten(seq, ctx, arena, out, 0);
}

namespace {

// §16.12.18: the declaration holding the sequence_expr an operand was
// substituted with, where the operand referenced a formal whose actual is
// one; nullptr for any other operand.
const ModuleItem* SequenceActual(const Expr* operand) {
  if (operand == nullptr || operand->property_actual == nullptr) return nullptr;
  const PropertyExprNode* tree = operand->property_actual;
  if (tree->kind != PropertyExprNode::Kind::kSequence) return nullptr;
  return tree->sequence;
}

// One operand of a body with the actuals in the formals' places: the
// operand, the delay before it, its match items and its repetition.
struct SubstitutedOperand {
  Expr* operand;
  SeqCycleDelay delay;
  std::vector<SeqMatchAssign> items;
  SeqRepetition repetition;
  std::vector<EventExpr> clock;
};

SubstitutedOperand SubstituteOperand(const LinearSequence& body, size_t j,
                                     const ActualsByFormal& actuals,
                                     SimContext& ctx, Arena& arena) {
  return {SubstituteFormals(body.operands[j], actuals, arena),
          ResolveDelay(body.delays[j], actuals, ctx, arena),
          SubstituteMatchItems(body.match_items[j], actuals, arena),
          body.repetitions[j], OperandClock(body, j)};
}

// The substituted operand appended to `out`, or, where it references a
// formal whose actual is a sequence_expr, that sequence's flattened
// operands, the delay before the operand added to the first's and the
// operand's match items carried by the last.
void AppendSubstitutedOperand(SubstitutedOperand sub, SimContext& ctx,
                              Arena& arena, LinearSequence& out) {
  size_t first = out.operands.size();
  if (const ModuleItem* inner = SequenceActual(sub.operand)) {
    ExpandInstance({inner, sub.operand, sub.delay, sub.repetition, sub.clock},
                   ctx, arena, out, 0);
    if (out.operands.size() > first) {
      out.match_items.back().insert(out.match_items.back().end(),
                                    sub.items.begin(), sub.items.end());
      return;
    }
  }
  out.operands.push_back(sub.operand);
  out.delays.push_back(sub.delay);
  out.match_items.push_back(std::move(sub.items));
  out.repetitions.push_back(sub.repetition);
  PushOperandClock(out, sub.clock);
}

}  // namespace

Expr* LiteralOfValue(const Logic4Vec& value, Arena& arena) {
  std::string text = std::to_string(value.width) + "'" +
                     (value.is_signed ? "s" : "") + "b" + value.ToString();
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->text = {arena.AllocString(text.data(), text.size()), text.size()};
  literal->int_val = value.ToUint64();
  return literal;
}

LinearSequence SubstituteLinearSequence(const LinearSequence& body,
                                        const ActualsByFormal& actuals,
                                        SimContext& ctx, Arena& arena) {
  LinearSequence out = body;
  out.operands.clear();
  out.delays.clear();
  out.match_items.clear();
  out.repetitions.clear();
  out.operand_clocks.clear();
  out.operand_clock_index.clear();
  out.throughouts.clear();
  // Where each of the body's operands begins and ends among the substituted
  // ones, a sequence actual among them expanding to several.
  std::vector<size_t> begins;
  std::vector<size_t> ends;
  for (size_t j = 0; j < body.operands.size(); ++j) {
    begins.push_back(out.operands.size());
    AppendSubstitutedOperand(SubstituteOperand(body, j, actuals, ctx, arena),
                             ctx, arena, out);
    ends.push_back(out.operands.size() - 1);
  }
  for (SeqThroughout guard : body.throughouts) {
    guard.cond = SubstituteFormals(guard.cond, actuals, arena);
    guard.first = begins[guard.first];
    guard.last = ends[guard.last];
    out.throughouts.push_back(guard);
  }
  for (LinearSequence& inner : out.intersects) {
    inner = SubstituteLinearSequence(inner, actuals, ctx, arena);
  }
  for (LinearSequence& inner : out.conjuncts) {
    inner = SubstituteLinearSequence(inner, actuals, ctx, arena);
  }
  for (LinearSequence& inner : out.alternatives) {
    inner = SubstituteLinearSequence(inner, actuals, ctx, arena);
  }
  return out;
}

}  // namespace delta
