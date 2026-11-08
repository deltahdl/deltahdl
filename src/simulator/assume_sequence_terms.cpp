#include "simulator/assume_sequence_terms.h"

#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_locals.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

enum class SeqTermKind : uint8_t {
  kBool,
  kMatch,
  kWait,
  kThen,
  kOr,
  kAnd,
  kIntersect,
  kFirstMatch,
  kThroughout,
  kRepeat,
  kGoto,
  kBind,
};

struct SeqTerm {
  SeqTermKind kind = SeqTermKind::kMatch;
  Expr* expr = nullptr;
  const std::vector<SeqMatchAssign>* items = nullptr;
  uint32_t lo = 0;
  uint32_t hi = 0;
  uint32_t count = 0;
  int clock = 0;
  uint8_t flags = 0;
  std::vector<const SeqTerm*> operands;
  const LocalValues* locals = nullptr;
  mutable std::map<uint64_t, std::vector<SeqWay>> ways;
};

namespace {

using Kind = SeqTermKind;

constexpr uint32_t kUnbounded = SeqCycleDelay::kUnbounded;
constexpr uint8_t kNonconsecutive = 1;
constexpr uint8_t kTail = 2;
constexpr uint8_t kNullable = 4;

std::string Id(const void* p) {
  return std::to_string(reinterpret_cast<uintptr_t>(p));
}

std::string KeyOf(const SeqTerm& term) {
  std::string key = std::to_string(static_cast<int>(term.kind)) + ':' +
                    Id(term.expr) + ':' + Id(term.items) + ':' +
                    std::to_string(term.lo) + ':' + std::to_string(term.hi) +
                    ':' + std::to_string(term.count) + ':' +
                    std::to_string(term.clock) + ':' +
                    std::to_string(term.flags) + ':' + Id(term.locals);
  for (const SeqTerm* op : term.operands) key += ',' + Id(op);
  return key;
}

std::string KeyOf(const std::vector<Logic4Vec>& values, const void* decls) {
  std::string key = Id(decls);
  for (const Logic4Vec& v : values) {
    key += ';' + std::to_string(v.width) + '/' +
           std::to_string(static_cast<int>(v.is_signed));
    for (uint32_t w = 0; w < v.nwords; ++w) {
      key += '/' + std::to_string(v.words[w].aval) + '.' +
             std::to_string(v.words[w].bval);
    }
  }
  return key;
}

bool Ticked(uint32_t ticked, int clock) {
  return ((ticked >> clock) & 1u) != 0;
}

uint32_t Less(uint32_t bound) {
  if (bound == kUnbounded) return kUnbounded;
  return bound > 0 ? bound - 1 : 0;
}

SeqWay Joined(const SeqWay& first, const SeqWay& then) {
  SeqWay way = then;
  way.literals.insert(way.literals.begin(), first.literals.begin(),
                      first.literals.end());
  way.items.insert(way.items.begin(), first.items.begin(), first.items.end());
  return way;
}

}  // namespace

int NumberClock(const std::vector<EventExpr>& clock, int inherited,
                const ObligationRewrite& rewrite,
                const ClockNumbering& clocks) {
  if (clock.empty()) return inherited;
  std::vector<EventExpr> rewritten = clock;
  for (EventExpr& ev : rewritten) {
    ev.signal = rewrite(ev.signal);
    ev.iff_condition = rewrite(ev.iff_condition);
  }
  return clocks(rewritten);
}

ConditionBuilder::ConditionBuilder(Arena& arena) : arena_(arena) {
  always_ = LiteralOfValue(MakeLogic4VecVal(arena, 1, 1), arena);
  never_ = LiteralOfValue(MakeLogic4VecVal(arena, 1, 0), arena);
}

Expr* ConditionBuilder::Not(Expr* a) {
  if (a == always_) return never_;
  if (a == never_) return always_;
  auto* e = arena_.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = TokenKind::kBang;
  e->lhs = a;
  return e;
}

Expr* ConditionBuilder::Join(Expr* a, Expr* b, bool conjunction) {
  Expr* unit = conjunction ? always_ : never_;
  Expr* zero = conjunction ? never_ : always_;
  if (a == zero || b == zero) return zero;
  if (a == unit) return b;
  if (b == unit) return a;
  auto* e = arena_.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = conjunction ? TokenKind::kAmpAmp : TokenKind::kPipePipe;
  e->lhs = a;
  e->rhs = b;
  return e;
}

Expr* ConditionBuilder::And(Expr* a, Expr* b) { return Join(a, b, true); }

Expr* ConditionBuilder::Or(Expr* a, Expr* b) { return Join(a, b, false); }

Expr* ConditionBuilder::AllOf(
    const std::vector<std::pair<Expr*, bool>>& literals) {
  Expr* all = always_;
  for (const auto& [operand, value] : literals) {
    all = And(all, value ? operand : Not(operand));
  }
  return all;
}

SeqTerms::SeqTerms(SimContext& ctx, Arena& arena, ConditionBuilder& conditions)
    : ctx_(ctx), arena_(arena), conditions_(conditions) {
  match_ = Make(Kind::kMatch, {});
}

SeqTerms::~SeqTerms() = default;

const SeqTerm* SeqTerms::Intern(SeqTerm term) {
  std::string key = KeyOf(term);
  auto& slot = terms_[key];
  if (slot == nullptr) slot = std::make_unique<SeqTerm>(std::move(term));
  return slot.get();
}

const SeqTerm* SeqTerms::Make(Kind kind, std::vector<const SeqTerm*> operands,
                              const SeqTermShape& shape) {
  SeqTerm term;
  term.kind = kind;
  term.operands = std::move(operands);
  term.expr = shape.expr;
  term.lo = shape.lo;
  term.hi = shape.hi;
  term.count = shape.count;
  term.clock = shape.clock;
  term.flags = shape.flags;
  return Intern(std::move(term));
}

const SeqTerm* SeqTerms::Wait(uint32_t lo, uint32_t hi, const SeqTerm* x,
                              int clock) {
  return Make(Kind::kWait, {x}, {.lo = lo, .hi = hi, .clock = clock});
}

const SeqTerm* SeqTerms::Bind(const LocalValues* locals, const SeqTerm* x) {
  SeqTerm term;
  term.kind = Kind::kBind;
  term.operands = {x};
  term.locals = locals;
  return Intern(std::move(term));
}

const LocalValues* SeqTerms::Locals(std::vector<Logic4Vec> values,
                                    const std::vector<SeqLocalDecl>* decls) {
  std::string key = KeyOf(values, decls);
  auto& slot = locals_[key];
  if (slot == nullptr) {
    slot = std::make_unique<LocalValues>();
    for (size_t i = 0; i < values.size(); ++i) {
      slot->references[(*decls)[i].name] =
          LocalReference((*decls)[i], values[i]);
    }
    slot->values = std::move(values);
    slot->decls = decls;
  }
  return slot.get();
}

bool SeqTerms::Nullable(const SeqTerm* term) {
  return (term->flags & kNullable) != 0;
}

int SeqTerms::FirstClock(const SeqTerm* term) {
  switch (term->kind) {
    case Kind::kBool:
    case Kind::kWait:
    case Kind::kThroughout:
    case Kind::kGoto:
      return term->clock;
    default:
      return FirstClock(term->operands[0]);
  }
}

Expr* SeqTerms::LocalReference(SeqLocalDecl decl, const Logic4Vec& value) {
  std::string name =
      std::string(decl.name) + "@v" + std::to_string(local_vars_.size());
  decl.name = {arena_.AllocString(name.data(), name.size()), name.size()};
  ctx_.PushScope();
  local_vars_[decl.name] = StandUpLocal(decl, value, ctx_);
  ctx_.PopScope();
  auto* reference = arena_.Create<Expr>();
  reference->kind = ExprKind::kIdentifier;
  reference->text = decl.name;
  return reference;
}

void SeqTerms::BindLocalsOf(const Expr* e) {
  ForEachSubExpr(e, [this](const Expr* sub) {
    if (sub->kind != ExprKind::kIdentifier) return;
    auto found = local_vars_.find(sub->text);
    if (found != local_vars_.end()) {
      ctx_.BindLocalVariable(found->first, found->second);
    }
  });
}

Expr* SeqTerms::UnderLocals(Expr* e, const LocalValues* locals) {
  return SubstituteFormals(e, locals->references, arena_);
}

const std::vector<SeqWay>& SeqTerms::Ways(const SeqTerm* term, uint32_t ticked,
                                          bool anchor) {
  uint64_t key =
      (static_cast<uint64_t>(ticked) << 1) | static_cast<uint64_t>(anchor);
  auto found = term->ways.find(key);
  if (found != term->ways.end()) return found->second;
  std::vector<SeqWay> out;
  Expand(term, ticked, anchor, out);
  return term->ways.emplace(key, std::move(out)).first->second;
}

void SeqTerms::Expand(const SeqTerm* term, uint32_t ticked, bool anchor,
                      std::vector<SeqWay>& out) {
  switch (term->kind) {
    case Kind::kBool:
      if (Ticked(ticked, term->clock)) {
        out.push_back({{{term->expr, true}}, nullptr, {term->items}});
      } else {
        out.push_back({{}, term, {}});
      }
      return;
    case Kind::kWait:
      ExpandWait(term, ticked, anchor, out);
      return;
    case Kind::kThen:
      ExpandThen(term, ticked, anchor, out);
      return;
    case Kind::kOr:
      for (const SeqTerm* op : term->operands) {
        const std::vector<SeqWay>& ways = Ways(op, ticked, anchor);
        out.insert(out.end(), ways.begin(), ways.end());
      }
      return;
    case Kind::kAnd:
    case Kind::kIntersect:
      ExpandPair(term, ticked, anchor, out);
      return;
    case Kind::kFirstMatch:
      ExpandFirstMatch(term, ticked, anchor, out);
      return;
    case Kind::kRepeat:
      ExpandRepeat(term, ticked, anchor, out);
      return;
    case Kind::kGoto:
      if (Ticked(ticked, term->clock)) {
        ExpandGoto(term, out);
      } else {
        out.push_back({{}, term, {}});
      }
      return;
    case Kind::kBind:
      ExpandBind(term, ticked, anchor, out);
      return;
    case Kind::kThroughout:
      ExpandThroughout(term, ticked, anchor, out);
      return;
    default:
      out.push_back({{}, nullptr, {}});
      return;
  }
}

void SeqTerms::ExpandThroughout(const SeqTerm* term, uint32_t ticked,
                                bool anchor, std::vector<SeqWay>& out) {
  bool reads = Ticked(ticked, term->clock);
  for (SeqWay way : Ways(term->operands[0], ticked, anchor)) {
    if (reads) way.literals.emplace_back(term->expr, true);
    if (way.next != nullptr) {
      way.next = Make(Kind::kThroughout, {way.next},
                      {.expr = term->expr, .clock = term->clock});
    }
    out.push_back(std::move(way));
  }
}

void SeqTerms::ExpandWait(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  const SeqTerm* x = term->operands[0];
  const SeqTerm* shifted = Wait(Less(term->lo), Less(term->hi), x, term->clock);
  if (!Ticked(ticked, term->clock)) {
    out.push_back({{}, anchor ? shifted : term, {}});
    return;
  }
  if (term->lo > 0 || term->hi > 0) out.push_back({{}, shifted, {}});
  if (term->lo > 0) return;
  const std::vector<SeqWay>& ways = Ways(x, ticked, true);
  out.insert(out.end(), ways.begin(), ways.end());
}

void SeqTerms::ExpandThen(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  const SeqTerm* a = term->operands[0];
  const SeqTerm* b = term->operands[1];
  int clock = FirstClock(b);
  bool past_empty = term->hi > 0;
  uint32_t lo = term->lo > 0 ? term->lo - 1 : 0;
  for (const SeqWay& way : Ways(a, ticked, anchor)) {
    if (way.next != nullptr) {
      out.push_back(
          {way.literals,
           Make(Kind::kThen, {way.next, b}, {.lo = term->lo, .hi = term->hi}),
           way.items});
      continue;
    }
    for (const SeqWay& then :
         Ways(Wait(term->lo, term->hi, b, clock), ticked, true)) {
      out.push_back(Joined(way, then));
    }
    if (!past_empty || !Nullable(b)) continue;
    for (const SeqWay& then :
         Ways(Wait(lo, Less(term->hi), match_, clock), ticked, true)) {
      out.push_back(Joined(way, then));
    }
  }
  if (!past_empty || !Nullable(a)) return;
  const std::vector<SeqWay>& ways =
      Ways(Wait(lo, Less(term->hi), b, clock), ticked, anchor);
  out.insert(out.end(), ways.begin(), ways.end());
}

void SeqTerms::ExpandPair(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  bool conjunction = term->kind == Kind::kAnd;
  const std::vector<SeqWay>& left = Ways(term->operands[0], ticked, anchor);
  const std::vector<SeqWay>& right = Ways(term->operands[1], ticked, anchor);
  for (const SeqWay& a : left) {
    for (const SeqWay& b : right) {
      bool one_matched = (a.next == nullptr) != (b.next == nullptr);
      if (one_matched && !conjunction) continue;
      SeqWay way = Joined(a, b);
      way.next = PairedNext(term->kind, a.next, b.next);
      out.push_back(std::move(way));
    }
  }
}

const SeqTerm* SeqTerms::PairedNext(Kind kind, const SeqTerm* a,
                                    const SeqTerm* b) {
  if (a == nullptr) return b;
  if (b == nullptr) return a;
  return Make(kind, {a, b});
}

void SeqTerms::ExpandFirstMatch(const SeqTerm* term, uint32_t ticked,
                                bool anchor, std::vector<SeqWay>& out) {
  const std::vector<SeqWay>& ways = Ways(term->operands[0], ticked, anchor);
  Expr* matched = conditions_.Never();
  for (const SeqWay& way : ways) {
    if (way.next == nullptr) {
      matched = conditions_.Or(matched, conditions_.AllOf(way.literals));
    }
  }
  for (SeqWay way : ways) {
    if (way.next != nullptr) {
      way.literals.emplace_back(matched, false);
      way.next = Make(Kind::kFirstMatch, {way.next});
    }
    out.push_back(std::move(way));
  }
}

void SeqTerms::ExpandRepeat(const SeqTerm* term, uint32_t ticked, bool anchor,
                            std::vector<SeqWay>& out) {
  const SeqTerm* body = term->operands[0];
  for (const SeqWay& way : Ways(term->operands[1], ticked, anchor)) {
    if (way.next != nullptr) {
      out.push_back(
          {way.literals,
           Make(Kind::kRepeat, {body, way.next},
                {.lo = term->lo, .hi = term->hi, .count = term->count}),
           way.items});
      continue;
    }
    uint32_t done = term->count + 1;
    if (done >= term->lo) out.push_back(way);
    if (done >= term->hi) continue;
    out.push_back({way.literals,
                   Make(Kind::kRepeat, {body, body},
                        {.lo = term->lo, .hi = term->hi, .count = done}),
                   way.items});
  }
}

void SeqTerms::ExpandGoto(const SeqTerm* term, std::vector<SeqWay>& out) {
  Expr* e = term->expr;
  if ((term->flags & kTail) != 0) {
    out.push_back({{{e, false}}, nullptr, {}});
    out.push_back({{{e, false}}, term, {}});
    return;
  }
  out.push_back({{{e, false}}, term, {}});
  uint32_t done = term->count + 1;
  auto counted = [&](uint8_t flags) {
    SeqTerm next = *term;
    next.ways.clear();
    next.count = done;
    next.flags = flags;
    return Intern(std::move(next));
  };
  if (done < term->hi) {
    out.push_back(
        {{{e, true}}, counted(term->flags & kNonconsecutive), {term->items}});
  }
  if (done < term->lo) return;
  out.push_back({{{e, true}}, nullptr, {term->items}});
  if ((term->flags & kNonconsecutive) != 0) {
    out.push_back(
        {{{e, true}}, counted(kNonconsecutive | kTail), {term->items}});
  }
}

void SeqTerms::ExpandBind(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  const LocalValues* locals = term->locals;
  for (const SeqWay& way : Ways(term->operands[0], ticked, anchor)) {
    SeqWay bound;
    for (const auto& [e, value] : way.literals) {
      bound.literals.emplace_back(UnderLocals(e, locals), value);
    }
    bound.items = way.items;
    bound.locals = locals;
    if (way.next != nullptr) bound.next = Bind(locals, way.next);
    out.push_back(std::move(bound));
  }
}

namespace {

void PerformMatchItem(const SeqMatchAssign& item, LocalValues& locals,
                      SimContext& ctx, Arena& arena) {
  const std::vector<SeqLocalDecl>& decls = *locals.decls;
  for (size_t i = 0; i < decls.size(); ++i) {
    if (decls[i].name != item.lvar) continue;
    ctx.PushScope();
    for (size_t k = 0; k < decls.size(); ++k) {
      StandUpLocal(decls[k], locals.values[k], ctx);
    }
    Variable& local = *ctx.FindLocalVariable(item.lvar);
    AssignMatchItem(item, EvalExpr(item.rhs, ctx, arena), local, ctx, arena);
    locals.values[i] = local.value;
    locals.values[i].is_signed = local.is_signed;
    ctx.PopScope();
  }
}

}  // namespace

void PerformMatchItems(
    const std::vector<const std::vector<SeqMatchAssign>*>& items,
    LocalValues& locals, SimContext& ctx, Arena& arena) {
  for (const std::vector<SeqMatchAssign>* group : items) {
    for (const SeqMatchAssign& item : *group) {
      PerformMatchItem(item, locals, ctx, arena);
    }
  }
}

const SeqTerm* SeqTerms::Take(const SeqWay& way) {
  if (way.locals == nullptr) return way.next;
  LocalValues locals = *way.locals;
  PerformMatchItems(way.items, locals, ctx_, arena_);
  return Bind(Locals(std::move(locals.values), locals.decls),
              way.next->operands[0]);
}

struct SeqTerms::Builder {
  SeqTerms& terms;
  const ObligationScope& scope;
  std::vector<Expr*>& reads;

  Expr* Read(Expr* e) {
    Expr* read = scope.rewrite(e);
    reads.push_back(read);
    return read;
  }

  int ClockOf(const std::vector<EventExpr>& clock, int inherited) {
    return NumberClock(clock, inherited, scope.rewrite, scope.clocks);
  }

  const SeqTerm* Body(const LinearSequence& s, int clock) {
    int own = ClockOf(s.declared_clock, clock);
    const SeqTerm* body = Operand(s, own);
    for (const LinearSequence& alt : s.alternatives) {
      body = terms.Make(Kind::kOr, {body, Operand(alt, own)});
    }
    if (!s.first_match) return body;
    return terms.Make(Kind::kFirstMatch, {body});
  }

  const SeqTerm* Operand(const LinearSequence& s, int clock) {
    const SeqTerm* all = Group(s, clock);
    for (const LinearSequence& conj : s.conjuncts) {
      all = terms.Make(Kind::kAnd, {all, Group(conj, clock)});
    }
    return all;
  }

  const SeqTerm* Group(const LinearSequence& s, int clock) {
    const SeqTerm* all = Chain(s, clock);
    for (const LinearSequence& inter : s.intersects) {
      all = terms.Make(Kind::kIntersect, {all, Chain(inter, clock)});
    }
    return all;
  }

  struct Part {
    const SeqTerm* term = nullptr;
    uint32_t lead = 0;
  };

  const SeqTerm* Chain(const LinearSequence& s, int clock) {
    Part part = Range(s, 0, s.operands.size() - 1, 0, clock);
    const SeqCycleDelay& d = s.delays[0];
    return terms.Wait(d.min - part.lead, Shorter(d.max, part.lead), part.term,
                      terms.FirstClock(part.term));
  }

  static uint32_t Shorter(uint32_t bound, uint32_t by) {
    return bound == kUnbounded ? kUnbounded : bound - by;
  }

  static size_t SpanAt(const LinearSequence& s, size_t i, size_t from) {
    for (size_t k = from; k < s.throughouts.size(); ++k) {
      if (s.throughouts[k].first == i) return k;
    }
    return s.throughouts.size();
  }

  Part Range(const LinearSequence& s, size_t i, size_t j, size_t from,
             int clock) {
    Part head;
    size_t last = i;
    size_t span = SpanAt(s, i, from);
    if (span < s.throughouts.size()) {
      const SeqThroughout& guard = s.throughouts[span];
      Part inner = Range(s, i, guard.last, span + 1, clock);
      int first = terms.FirstClock(inner.term);
      uint32_t wait = guard.lead - inner.lead;
      head.term = terms.Make(Kind::kThroughout,
                             {terms.Wait(wait, wait, inner.term, first)},
                             {.expr = Read(guard.cond), .clock = first});
      head.lead = guard.lead;
      last = guard.last;
    } else {
      head.term = Item(s, i, clock);
    }
    if (last == j) return head;
    Part rest = Range(s, last + 1, j, 0, clock);
    const SeqCycleDelay& d = s.delays[last + 1];
    head.term =
        terms.Make(Kind::kThen, {head.term, rest.term},
                   {.lo = d.min - rest.lead, .hi = Shorter(d.max, rest.lead)});
    return head;
  }

  const SeqTerm* Item(const LinearSequence& s, size_t i, int clock) {
    int own = ClockOf(OperandClock(s, i), clock);
    const SeqRepetition& rep = s.repetitions[i];
    const std::vector<SeqMatchAssign>& items = s.match_items[i];
    bool repeated = rep.kind != SeqRepetition::Kind::kNone;
    auto nullable = static_cast<uint8_t>((rep.min == 0) * kNullable);
    if (rep.kind == SeqRepetition::Kind::kGoto ||
        rep.kind == SeqRepetition::Kind::kNonconsecutive) {
      auto nonconsecutive = static_cast<uint8_t>(
          (rep.kind == SeqRepetition::Kind::kNonconsecutive) * kNonconsecutive);
      SeqTerm term;
      term.kind = Kind::kGoto;
      term.expr = Read(s.operands[i]);
      term.items = &items;
      term.lo = rep.min;
      term.hi = rep.max;
      term.clock = own;
      term.flags = static_cast<uint8_t>(nonconsecutive | nullable);
      return terms.Intern(std::move(term));
    }
    const LinearSequence* nested = NestedOperand(s, i);
    const SeqTerm* base =
        nested != nullptr ? Body(*nested, own) : Bool(s, i, own, items);
    if (!repeated) return base;
    return terms.Make(Kind::kRepeat, {base, base},
                      {.lo = rep.min, .hi = rep.max, .flags = nullable});
  }

  const SeqTerm* Bool(const LinearSequence& s, size_t i, int clock,
                      const std::vector<SeqMatchAssign>& items) {
    SeqTerm term;
    term.kind = Kind::kBool;
    term.expr = Read(s.operands[i]);
    term.items = &items;
    term.clock = clock;
    return terms.Intern(std::move(term));
  }
};

namespace {

void CollectLocals(const LinearSequence& s, std::vector<SeqLocalDecl>& out) {
  out.insert(out.end(), s.locals.begin(), s.locals.end());
  for (const auto* list : {&s.alternatives, &s.conjuncts, &s.intersects}) {
    for (const LinearSequence& inner : *list) CollectLocals(inner, out);
  }
  for (const auto& entry : s.nested) CollectLocals(*entry.second, out);
}

}  // namespace

const SeqTerm* SeqTerms::Begin(const ModuleItem* item, int clock,
                               const ObligationScope& scope,
                               std::vector<Expr*>& reads, int& clock_out) {
  auto seq = std::make_unique<LinearSequence>();
  if (!FlattenLinearSequence(item, ctx_, arena_, *seq)) return nullptr;
  Builder builder{*this, scope, reads};
  const SeqTerm* term = builder.Body(*seq, clock);
  auto decls = std::make_unique<std::vector<SeqLocalDecl>>();
  CollectLocals(*seq, *decls);
  if (!decls->empty()) {
    term = Bind(Locals(InitialLocals(*decls, ctx_, arena_), decls.get()), term);
  }
  local_decls_.push_back(std::move(decls));
  clock_out = builder.ClockOf(seq->clock_out, clock);
  sequences_.push_back(std::move(seq));
  return term;
}

}  // namespace delta
