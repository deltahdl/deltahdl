#include "simulator/sequence_flatten.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/sequence_actual_cast.h"
#include "simulator/sequence_locals.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

constexpr int kMaxInstanceDepth = 16;

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
    copy.target = SubstituteFormals(item.target, actuals, arena);
    if (item.call != nullptr) {
      copy.call = SubstituteFormals(item.call, actuals, arena);
    }
    out.push_back(copy);
  }
  return out;
}

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

template <typename Names>
bool NamesAny(const Expr* expr, const Names& names) {
  bool named = false;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind != ExprKind::kIdentifier) return;
    for (const auto& name : names) {
      if (e->text == name) named = true;
    }
  });
  return named;
}

bool NamesOnlyVariables(const Expr* expr, SimContext& ctx) {
  bool declared = true;
  ForEachSubExpr(expr, [&](const Expr* e) {
    if (e->kind == ExprKind::kIdentifier &&
        ctx.FindVariable(e->text) == nullptr) {
      declared = false;
    }
  });
  return declared;
}

void ResolveDelayBound(uint32_t& bound, Expr*& expr,
                       const ActualsByFormal& actuals, SimContext& ctx,
                       Arena& arena) {
  if (expr == nullptr) return;
  std::vector<std::string_view> formals;
  for (const auto& [formal, actual] : actuals) {
    if (actual != nullptr) formals.push_back(formal);
  }
  if (!NamesAny(expr, formals)) return;
  const Expr* actual = SubstituteFormals(expr, actuals, arena);
  expr = nullptr;
  if (actual->kind == ExprKind::kIdentifier && actual->text == "$") {
    bound = SeqCycleDelay::kUnbounded;
    return;
  }
  Logic4Vec value = EvalExpr(actual, ctx, arena);
  if (!value.IsKnown()) return;
  bound = static_cast<uint32_t>(value.ToUint64());
}

template <typename Bounds>
Bounds ResolveBounds(Bounds bounds, const ActualsByFormal& actuals,
                     SimContext& ctx, Arena& arena) {
  ResolveDelayBound(bounds.min, bounds.min_expr, actuals, ctx, arena);
  ResolveDelayBound(bounds.max, bounds.max_expr, actuals, ctx, arena);
  return bounds;
}

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

ActualsByFormal BindInstanceActuals(const ModuleItem* decl,
                                    const Expr* instance, Arena& arena) {
  ActualsByFormal actuals = BindActualsWithDefaults(
      decl->prop_formals, decl->prop_formal_defaults, instance);
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_type_kw.size();
       ++i) {
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end()) continue;
    it->second = CastActualToFormal(it->second, decl->prop_formal_type_kw[i],
                                    decl->prop_formal_types[i], arena);
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
        copy.iff_condition =
            SubstituteFormals(ev.iff_condition, actuals, arena);
        AppendActualEvents(copy, it->second, arena, out);
        continue;
      }
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
  std::string name = InstanceDeclName(operand);
  return name.empty() ? nullptr : ctx.FindSequenceDecl(name);
}

bool Flatten(const ModuleItem* seq, SimContext& ctx, Arena& arena,
             LinearSequence& out, int depth);

struct InstanceOperand {
  const ModuleItem* inner;
  const Expr* instance;
  SeqCycleDelay before;
  SeqRepetition repetition;
  std::vector<EventExpr> clock;
  std::vector<SeqMatchAssign> items;
};

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

bool UnrollInstanceRepetition(LinearSequence& out, size_t first,
                              const SeqRepetition& rep) {
  if (rep.kind == SeqRepetition::Kind::kNone) return true;
  if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
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

struct LocalBinding {
  std::string_view renamed;
  Expr* actual;
  Direction direction;
};

struct Renaming {
  int instance;
  LinearSequence& out;
  Arena& arena;
};

LocalBinding RenameLocalFormal(const ModuleItem* inner, const LocalFormal& lf,
                               ActualsByFormal& actuals, Renaming& renaming) {
  std::string_view name = inner->prop_formals[lf.index];
  LocalBinding binding;
  binding.renamed = RenamedLocal(name, renaming.instance, renaming.arena);
  auto it = actuals.find(name);
  binding.actual = it == actuals.end() ? nullptr : it->second;
  binding.direction = lf.direction;
  SeqLocalDecl decl = LocalFormalDecl(*inner, lf.index);
  decl.name = binding.renamed;
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

const ModuleItem* SequenceActual(const Expr* operand) {
  if (operand == nullptr) return nullptr;
  const PropertyExprNode* tree = ActualTree(operand);
  if (tree == nullptr || tree->kind != PropertyExprNode::Kind::kSequence) {
    return nullptr;
  }
  return tree->sequence;
}

const ModuleItem* SequenceActualOf(const Expr* operand, SimContext& ctx) {
  if (ActualTree(operand) == nullptr) return InstantiatedSequence(operand, ctx);
  return SequenceActual(operand);
}

bool ExpandInstance(const InstanceOperand& op, SimContext& ctx, Arena& arena,
                    LinearSequence& out, int depth);

struct SubstitutedOperand {
  Expr* operand;
  SeqCycleDelay delay;
  std::vector<SeqMatchAssign> items;
  SeqRepetition repetition;
  std::vector<EventExpr> clock;
};

void ReadClockedBooleanActual(Expr*& operand, std::vector<EventExpr>& clock) {
  const PropertyExprNode* tree =
      operand != nullptr ? ActualTree(operand) : nullptr;
  if (tree == nullptr || tree->kind != PropertyExprNode::Kind::kBoolean ||
      tree->boolean == nullptr || tree->clock.empty()) {
    return;
  }
  operand = tree->boolean;
  clock = tree->clock;
}

void AppendOperand(SubstitutedOperand sub, LinearSequence& out) {
  out.operands.push_back(sub.operand);
  out.delays.push_back(sub.delay);
  out.match_items.push_back(std::move(sub.items));
  out.repetitions.push_back(sub.repetition);
  PushOperandClock(out, sub.clock);
}

void AttachInstanceItems(LinearSequence& out,
                         const std::vector<SeqMatchAssign>& items,
                         Arena& arena) {
  if (items.empty()) return;
  if (out.repetitions.back().kind != SeqRepetition::Kind::kNone) {
    auto* one = arena.Create<Expr>();
    one->kind = ExprKind::kIntegerLiteral;
    one->text = "1";
    one->int_val = 1;
    SeqCycleDelay fused;
    fused.min = 0;
    fused.max = 0;
    std::vector<EventExpr> clock = OperandClock(out, out.operands.size() - 1);
    AppendOperand({one, fused, {}, SeqRepetition{}, clock}, out);
  }
  auto& last = out.match_items.back();
  last.insert(last.end(), items.begin(), items.end());
}

void AddNested(LinearSequence& out, const Expr* operand,
               LinearSequence nested) {
  out.nested.emplace_back(
      operand, std::make_shared<const LinearSequence>(std::move(nested)));
}

void AdoptInstanceClock(const LinearSequence& body,
                        const ActualsByFormal& actuals, Arena& arena,
                        LinearSequence& out) {
  if (out.clock.empty() && !body.clock.empty()) {
    out.clock = SubstituteClock(body.clock, actuals, arena);
  }
}

struct Expansion {
  const InstanceOperand& op;
  const LinearSequence& body;
  const ActualsByFormal& actuals;
  SimContext& ctx;
  Arena& arena;
  int depth;
};

bool AppendInstanceOperand(const Expansion& x, size_t j, LinearSequence& out) {
  const LinearSequence& body = x.body;
  const InstanceOperand& op = x.op;
  const ActualsByFormal& actuals = x.actuals;
  SimContext& ctx = x.ctx;
  Arena& arena = x.arena;
  Expr* operand = SubstituteFormals(body.operands[j], actuals, arena);
  SeqCycleDelay delay = ResolveBounds(body.delays[j], actuals, ctx, arena);
  if (j == 0) delay = AddDelays(op.before, delay);
  SeqRepetition repetition =
      ResolveBounds(body.repetitions[j], actuals, ctx, arena);
  std::vector<EventExpr> clock =
      InstanceOperandClock(body, j, op, actuals, arena);
  std::vector<SeqMatchAssign> items =
      SubstituteMatchItems(body.match_items[j], actuals, arena);
  if (const LinearSequence* nested = NestedOperand(body, j)) {
    AddNested(out, body.operands[j],
              SubstituteLinearSequence(*nested, actuals, ctx, arena));
    AppendOperand(
        {body.operands[j], delay, std::move(items), repetition, clock}, out);
    return true;
  }
  if (const ModuleItem* bound = SequenceActualOf(operand, ctx)) {
    return ExpandInstance({bound, operand, delay, repetition, clock, items},
                          ctx, arena, out, x.depth + 1);
  }
  ReadClockedBooleanActual(operand, clock);
  AppendOperand({operand, delay, std::move(items), repetition, clock}, out);
  return true;
}

bool AppendNestedOperand(const InstanceOperand& op, const LinearSequence& body,
                         SimContext& ctx, Arena& arena, LinearSequence& out) {
  ActualsByFormal actuals = BindInstanceActuals(op.inner, op.instance, arena);
  AdoptInstanceClock(body, actuals, arena, out);
  size_t first = out.operands.size();
  Expr* operand = arena.Create<Expr>(*op.instance);
  AddNested(out, operand, SubstituteLinearSequence(body, actuals, ctx, arena));
  bool kept = op.repetition.IteratesWhole();
  SeqRepetition repetition = kept ? op.repetition : SeqRepetition{};
  AppendOperand({operand, op.before, op.items, repetition, op.clock}, out);
  return kept || UnrollInstanceRepetition(out, first, op.repetition);
}

bool ExpandInstance(const InstanceOperand& op, SimContext& ctx, Arena& arena,
                    LinearSequence& out, int depth) {
  LinearSequence body;
  if (!Flatten(op.inner, ctx, arena, body, depth + 1)) return false;
  if (!body.alternatives.empty() || !body.conjuncts.empty() ||
      !body.intersects.empty() || op.repetition.IteratesWhole()) {
    return AppendNestedOperand(op, body, ctx, arena, out);
  }
  ActualsByFormal actuals = BindInstanceActuals(op.inner, op.instance, arena);
  Renaming renaming{static_cast<int>(out.operands.size()) + 1, out, arena};
  std::vector<LocalBinding> formals =
      RenameInstanceLocals(op.inner, body, actuals, renaming);
  AdoptInstanceClock(body, actuals, arena, out);
  size_t first = out.operands.size();
  std::vector<size_t> begins;
  std::vector<size_t> ends;
  Expansion expansion{op, body, actuals, ctx, arena, depth};
  for (size_t j = 0; j < body.operands.size(); ++j) {
    begins.push_back(out.operands.size());
    if (!AppendInstanceOperand(expansion, j, out)) return false;
    ends.push_back(out.operands.size() - 1);
  }
  for (SeqThroughout guard : body.throughouts) {
    guard.cond = SubstituteFormals(guard.cond, actuals, arena);
    guard.first = begins[guard.first];
    guard.last = ends[guard.last];
    out.throughouts.push_back(guard);
  }
  if (out.operands.size() == first) return true;
  AddLocalFormalAssignments(formals, out.match_items[first],
                            out.match_items.back(), arena);
  AttachInstanceItems(out, op.items, arena);
  return UnrollInstanceRepetition(out, first, op.repetition);
}

bool FlattenChain(const SeqLinearBody& body, SimContext& ctx, Arena& arena,
                  LinearSequence& out, int depth);

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

void AttachFirstMatchItems(const SeqLinearBody& body, LinearSequence& out) {
  if (body.first_match_items.empty()) return;
  for (const SeqMatchAssign& item : body.first_match_items) {
    out.match_items.back().push_back(item);
    for (LinearSequence& alt : out.alternatives) {
      alt.match_items.back().push_back(item);
    }
  }
}

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

bool FlattenChain(const SeqLinearBody& body, SimContext& ctx, Arena& arena,
                  LinearSequence& out, int depth) {
  out.locals = body.locals;
  std::vector<size_t> begins;
  std::vector<size_t> ends;
  for (size_t i = 0; i < body.operands.size(); ++i) {
    Expr* operand = body.operands[i];
    const SeqCycleDelay& before = body.delays[i];
    const ModuleItem* inner = SequenceActualOf(operand, ctx);
    begins.push_back(out.operands.size());
    if (inner == nullptr) {
      out.operands.push_back(operand);
      out.delays.push_back(before);
      out.match_items.push_back(body.match_items[i]);
      out.repetitions.push_back(body.repetitions[i]);
      PushOperandClock(out, BodyOperandClock(body, i));
    } else if (!ExpandInstance({inner, operand, before, body.repetitions[i],
                                BodyOperandClock(body, i), body.match_items[i]},
                               ctx, arena, out, depth)) {
      return false;
    }
    ends.push_back(out.operands.size() - 1);
  }
  for (SeqThroughout guard : body.throughouts) {
    guard.first = begins[guard.first];
    guard.last = ends[guard.last];
    out.throughouts.push_back(guard);
  }
  return true;
}

}  // namespace

namespace {

void ForEachBound(LinearSequence& seq,
                  const std::function<void(uint32_t&, Expr*&)>& fn) {
  for (SeqCycleDelay& delay : seq.delays) {
    fn(delay.min, delay.min_expr);
    fn(delay.max, delay.max_expr);
  }
  for (SeqRepetition& rep : seq.repetitions) {
    fn(rep.min, rep.min_expr);
    fn(rep.max, rep.max_expr);
  }
  for (auto* list : {&seq.intersects, &seq.conjuncts, &seq.alternatives}) {
    for (LinearSequence& inner : *list) ForEachBound(inner, fn);
  }
  for (auto& entry : seq.nested) {
    LinearSequence inner = *entry.second;
    ForEachBound(inner, fn);
    entry.second = std::make_shared<const LinearSequence>(std::move(inner));
  }
}

}  // namespace

bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out) {
  out = LinearSequence{};
  if (!Flatten(seq, ctx, arena, out, 0)) return false;
  if (const ActualsByFormal* checker =
          ctx.CheckerActuals(ctx.ActiveInstancePrefix())) {
    ForEachBound(out, [&](uint32_t& bound, Expr*& expr) {
      ResolveDelayBound(bound, expr, *checker, ctx, arena);
    });
  }
  ForEachBound(out, [&](uint32_t& bound, Expr*& expr) {
    if (expr == nullptr || NamesAny(expr, seq->prop_formals) ||
        !NamesOnlyVariables(expr, ctx)) {
      return;
    }
    Logic4Vec value = EvalExpr(expr, ctx, arena);
    if (!value.IsKnown()) return;
    expr = nullptr;
    bound = static_cast<uint32_t>(value.ToUint64());
  });
  return true;
}

ActualsByFormal CheckerTreeActuals(const std::string& inst_prefix,
                                   SimContext& ctx) {
  ActualsByFormal trees;
  if (const ActualsByFormal* checker = ctx.CheckerActuals(inst_prefix)) {
    for (const auto& [formal, actual] : *checker) {
      if (actual != nullptr &&
          (actual->property_actual != nullptr || IsEventActual(actual))) {
        trees[formal] = actual;
      }
    }
  }
  return trees;
}

const LinearSequence* NestedOperand(const LinearSequence& body, size_t pos) {
  for (const auto& [operand, nested] : body.nested) {
    if (operand == body.operands[pos]) return nested.get();
  }
  return nullptr;
}

namespace {

SubstitutedOperand SubstituteOperand(const LinearSequence& body, size_t j,
                                     const ActualsByFormal& actuals,
                                     SimContext& ctx, Arena& arena) {
  return {SubstituteFormals(body.operands[j], actuals, arena),
          ResolveBounds(body.delays[j], actuals, ctx, arena),
          SubstituteMatchItems(body.match_items[j], actuals, arena),
          ResolveBounds(body.repetitions[j], actuals, ctx, arena),
          OperandClock(body, j)};
}

void AppendSubstitutedOperand(SubstitutedOperand sub, SimContext& ctx,
                              Arena& arena, LinearSequence& out) {
  size_t first = out.operands.size();
  ReadClockedBooleanActual(sub.operand, sub.clock);
  if (const ModuleItem* inner = SequenceActual(sub.operand)) {
    ExpandInstance(
        {inner, sub.operand, sub.delay, sub.repetition, sub.clock, sub.items},
        ctx, arena, out, 0);
    if (out.operands.size() > first) return;
  }
  AppendOperand(std::move(sub), out);
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
  out.nested.clear();
  std::vector<size_t> begins;
  std::vector<size_t> ends;
  for (size_t j = 0; j < body.operands.size(); ++j) {
    begins.push_back(out.operands.size());
    SubstitutedOperand sub = SubstituteOperand(body, j, actuals, ctx, arena);
    if (const LinearSequence* nested = NestedOperand(body, j)) {
      sub.operand = body.operands[j];
      AddNested(out, sub.operand,
                SubstituteLinearSequence(*nested, actuals, ctx, arena));
      AppendOperand(std::move(sub), out);
    } else {
      AppendSubstitutedOperand(std::move(sub), ctx, arena, out);
    }
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
