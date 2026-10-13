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
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_locals.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// §16.7 to §16.10's operators as a term holds them: a boolean operand with
// the match items written with it; the match of the tick read; a wait of
// `lo` to `hi` ticks of `clock` before its operand; an operand followed by
// another `lo` to `hi` ticks after its match; or, and, intersect,
// first_match and throughout; a consecutive repetition from `lo` to `hi`
// times of its first operand, `count` matched and the second the current
// one; a goto repetition of `expr`, nonconsecutive where `flags` bit 0 is
// set and past its last match where bit 1 is; and an operand read under
// an attempt's local variables.
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

struct SeqLocals {
  std::vector<Logic4Vec> values;
  const std::vector<SeqLocalDecl>* decls = nullptr;
  // Each local's name with a literal of its value, and the expressions read
  // with those literals in the locals' places, each substituted once.
  ActualsByFormal literals;
  mutable std::map<const Expr*, Expr*> substituted;
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
  const SeqLocals* locals = nullptr;
  // The ways read at a tick, by the clocks that ticked and the anchor.
  mutable std::map<uint64_t, std::vector<SeqWay>> ways;
};

namespace {

using Kind = SeqTermKind;

constexpr uint32_t kUnbounded = SeqCycleDelay::kUnbounded;
constexpr uint8_t kNonconsecutive = 1;
constexpr uint8_t kTail = 2;

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
  return clock >= 32 || ((ticked >> clock) & 1u) != 0;
}

uint32_t Less(uint32_t bound) {
  if (bound == kUnbounded) return kUnbounded;
  return bound > 0 ? bound - 1 : 0;
}

// The way `first` took at this tick, matching there, followed at the same
// tick by the way `then` of what comes after it.
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
                              Expr* expr, uint32_t lo, uint32_t hi,
                              uint32_t count, int clock, uint8_t flags) {
  SeqTerm term;
  term.kind = kind;
  term.operands = std::move(operands);
  term.expr = expr;
  term.lo = lo;
  term.hi = hi;
  term.count = count;
  term.clock = clock;
  term.flags = flags;
  return Intern(std::move(term));
}

const SeqTerm* SeqTerms::Wait(uint32_t lo, uint32_t hi, const SeqTerm* x,
                              int clock) {
  return Make(Kind::kWait, {x}, nullptr, lo, hi, 0, clock);
}

const SeqTerm* SeqTerms::Bind(const SeqLocals* locals, const SeqTerm* x) {
  SeqTerm term;
  term.kind = Kind::kBind;
  term.operands = {x};
  term.locals = locals;
  return Intern(std::move(term));
}

const SeqLocals* SeqTerms::Locals(std::vector<Logic4Vec> values,
                                  const std::vector<SeqLocalDecl>* decls) {
  std::string key = KeyOf(values, decls);
  auto& slot = locals_[key];
  if (slot == nullptr) {
    slot = std::make_unique<SeqLocals>();
    for (size_t i = 0; i < values.size(); ++i) {
      slot->literals[(*decls)[i].name] = LiteralOfValue(values[i], arena_);
    }
    slot->values = std::move(values);
    slot->decls = decls;
  }
  return slot.get();
}

// §16.9.2.1: whether an attempt begun in `term` may match without reading a
// tick, as a repetition that may repeat zero times does.
bool SeqTerms::Nullable(const SeqTerm* term) {
  switch (term->kind) {
    case Kind::kOr:
      return Nullable(term->operands[0]) || Nullable(term->operands[1]);
    case Kind::kAnd:
    case Kind::kIntersect:
      return Nullable(term->operands[0]) && Nullable(term->operands[1]);
    case Kind::kFirstMatch:
    case Kind::kThroughout:
    case Kind::kBind:
      return Nullable(term->operands[0]);
    case Kind::kRepeat:
      return term->count == 0 && term->operands[0] == term->operands[1] &&
             (term->lo == 0 || Nullable(term->operands[0]));
    case Kind::kGoto:
      return term->count == 0 && term->flags < kTail && term->lo == 0;
    default:
      return false;
  }
}

// The clock the first tick an attempt begun in `term` reads is of.
int SeqTerms::FirstClock(const SeqTerm* term) {
  switch (term->kind) {
    case Kind::kBool:
    case Kind::kWait:
    case Kind::kThroughout:
    case Kind::kGoto:
    case Kind::kMatch:
      return term->clock;
    default:
      return FirstClock(term->operands[0]);
  }
}

Expr* SeqTerms::UnderLocals(Expr* e, const SeqLocals* locals) {
  auto& memo = locals->substituted;
  auto found = memo.find(e);
  if (found != memo.end()) return found->second;
  Expr* read = SubstituteFormals(e, locals->literals, arena_);
  memo[e] = read;
  return read;
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
      for (SeqWay way : Ways(term->operands[0], ticked, anchor)) {
        if (Ticked(ticked, term->clock)) {
          way.literals.emplace_back(term->expr, true);
        }
        if (way.next != nullptr) {
          way.next = Make(Kind::kThroughout, {way.next}, term->expr, 0, 0, 0,
                          term->clock);
        }
        out.push_back(std::move(way));
      }
      return;
    default:
      out.push_back({{}, nullptr, {}});
      return;
  }
}

// §16.7 and §16.13.1: a wait counts the ticks of its clock: at a tick of
// it, one tick passes and the operand is read once none is left to wait;
// at another time step the wait stands, but at the one it was begun at,
// which counts as the tick before the first it waits for.
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

// §16.7: `a ##[lo:hi] b`, b begun from lo to hi ticks after each match of
// a. §16.9.2.1: an a that may match empty also lets b begin from lo - 1 to
// hi - 1 ticks after the attempt begins, `empty ##n b` being `##(n-1) b`;
// a b that may match empty lets the whole match from lo - 1 to hi - 1 ticks
// after a's match, `a ##n empty` being `a ##(n-1) 1`; neither form follows
// a delay of ##0.
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
           Make(Kind::kThen, {way.next, b}, nullptr, term->lo, term->hi),
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

// §16.9.5 and §16.9.6: the attempts of both operands go on together; an
// intersect matches where both match at the same tick, and an and once
// both have matched, an operand that has matched leaving the other to go
// on alone.
void SeqTerms::ExpandPair(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  bool conjunction = term->kind == Kind::kAnd;
  const std::vector<SeqWay>& left = Ways(term->operands[0], ticked, anchor);
  const std::vector<SeqWay>& right = Ways(term->operands[1], ticked, anchor);
  for (const SeqWay& a : left) {
    for (const SeqWay& b : right) {
      SeqWay way = Joined(a, b);
      if (a.next != nullptr && b.next != nullptr) {
        way.next = Make(term->kind, {a.next, b.next});
      } else if (a.next != b.next) {
        if (!conjunction) continue;
        way.next = a.next != nullptr ? a.next : b.next;
      }
      out.push_back(std::move(way));
    }
  }
}

// §16.9.8: the attempt ends at the first tick it matches at, every match
// there being one; the ways going on past it go on only where none matches.
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

// §16.9.2: a consecutive repetition matches once from `lo` to `hi` of its
// operand's matches have followed one another, each beginning the tick
// after the one before it ended.
void SeqTerms::ExpandRepeat(const SeqTerm* term, uint32_t ticked, bool anchor,
                            std::vector<SeqWay>& out) {
  const SeqTerm* body = term->operands[0];
  if (term->hi == 0) return;
  for (const SeqWay& way : Ways(term->operands[1], ticked, anchor)) {
    if (way.next != nullptr) {
      out.push_back({way.literals,
                     Make(Kind::kRepeat, {body, way.next}, nullptr, term->lo,
                          term->hi, term->count),
                     way.items});
      continue;
    }
    uint32_t done = term->count + 1;
    if (done >= term->lo) out.push_back(way);
    if (term->hi != kUnbounded && done >= term->hi) continue;
    out.push_back(
        {way.literals,
         Make(Kind::kRepeat, {body, body}, nullptr, term->lo, term->hi, done),
         way.items});
  }
}

// §16.9.2: a goto repetition waits at the ticks its operand does not hold
// at and counts those it does, matching at the last of `lo` to `hi` of
// them; a nonconsecutive one also matches at each later tick it does not
// hold at, before it holds again.
void SeqTerms::ExpandGoto(const SeqTerm* term, std::vector<SeqWay>& out) {
  Expr* e = term->expr;
  if (term->flags >= kTail) {
    out.push_back({{{e, false}}, nullptr, {}});
    out.push_back({{{e, false}}, term, {}});
    return;
  }
  out.push_back({{{e, false}}, term, {}});
  uint32_t done = term->count + 1;
  auto counted = [&](uint8_t flags) {
    return Make(Kind::kGoto, {}, e, term->lo, term->hi, done, term->clock,
                flags);
  };
  if (term->hi == kUnbounded || done < term->hi) {
    out.push_back({{{e, true}}, counted(term->flags), {}});
  }
  if (done < term->lo) return;
  out.push_back({{{e, true}}, nullptr, {}});
  if (term->flags == kNonconsecutive) {
    out.push_back({{{e, true}}, counted(kNonconsecutive | kTail), {}});
  }
}

// §16.10: an operand under an attempt's locals reads each local as the
// value the attempt holds for it.
void SeqTerms::ExpandBind(const SeqTerm* term, uint32_t ticked, bool anchor,
                          std::vector<SeqWay>& out) {
  const SeqLocals* locals = term->locals;
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

// §16.10: one match item, `lvar = rhs` or `lvar op= rhs`, assigning the
// attempt's value of the local at the local's width; a subroutine call
// (§16.11) assigns none.
void SeqTerms::Assign(const SeqMatchAssign& item,
                      const std::vector<SeqLocalDecl>& decls,
                      std::vector<Logic4Vec>& values,
                      ActualsByFormal& literals) {
  for (size_t i = 0; i < decls.size(); ++i) {
    if (item.call != nullptr || decls[i].name != item.lvar) continue;
    Logic4Vec rhs =
        EvalExpr(SubstituteFormals(item.rhs, literals, arena_), ctx_, arena_);
    if (item.op != TokenKind::kEq) {
      rhs = EvalBinaryOp(CompoundAssignBaseOp(item.op), values[i], rhs, arena_);
    }
    bool is_signed = values[i].is_signed;
    values[i] =
        ResizeToWidth(OwnRhsWords(rhs, arena_), values[i].width, arena_);
    values[i].is_signed = is_signed;
    literals[decls[i].name] = LiteralOfValue(values[i], arena_);
  }
}

const SeqTerm* SeqTerms::Take(const SeqWay& way) {
  if (way.next == nullptr || way.locals == nullptr) return way.next;
  std::vector<Logic4Vec> values = way.locals->values;
  const std::vector<SeqLocalDecl>& decls = *way.locals->decls;
  ActualsByFormal literals = way.locals->literals;
  for (const std::vector<SeqMatchAssign>* items : way.items) {
    if (items == nullptr) continue;
    for (const SeqMatchAssign& item : *items) {
      Assign(item, decls, values, literals);
    }
  }
  return Bind(Locals(std::move(values), &decls), way.next->operands[0]);
}

// §16.7 to §16.10 and §16.13.1: a flattened sequence read into terms: its
// `or` operands, each the `and` of its chain's `intersect` groups, each the
// `intersect` of chains, a chain being its operands under their delays and
// repetitions, with the throughouts spanning them, and a nested operand a
// sequence of its own; each operand on the clock it names or the one
// flowing to it.
struct SeqTerms::Builder {
  SeqTerms& terms;
  const ObligationRewrite& rewrite;
  const ClockNumbering& clocks;
  std::vector<Expr*>& reads;
  // §16.10: whether the operands' match items assign the locals of the one
  // chain the sequence is.
  bool assigns_locals = false;

  // A chain's operands from one to another, and how many ticks before its
  // first operand the interval of a throughout beginning there begins.
  struct Part {
    const SeqTerm* term = nullptr;
    uint32_t lead = 0;
  };

  Expr* Read(Expr* e) {
    Expr* read = rewrite(e);
    reads.push_back(read);
    return read;
  }

  int ClockOf(const std::vector<EventExpr>& clock, int inherited) {
    return NumberClock(clock, inherited, rewrite, clocks);
  }

  const SeqTerm* Body(const LinearSequence& s, int clock) {
    int own = ClockOf(s.declared_clock, clock);
    const SeqTerm* body = Operand(s, own);
    for (const LinearSequence& alt : s.alternatives) {
      const SeqTerm* other = Operand(alt, own);
      if (body == nullptr || other == nullptr) return nullptr;
      body = terms.Make(Kind::kOr, {body, other});
    }
    if (body == nullptr || !s.first_match) return body;
    return terms.Make(Kind::kFirstMatch, {body});
  }

  const SeqTerm* Operand(const LinearSequence& s, int clock) {
    const SeqTerm* all = Group(s, clock);
    for (const LinearSequence& conj : s.conjuncts) {
      const SeqTerm* other = Group(conj, clock);
      if (all == nullptr || other == nullptr) return nullptr;
      all = terms.Make(Kind::kAnd, {all, other});
    }
    return all;
  }

  const SeqTerm* Group(const LinearSequence& s, int clock) {
    const SeqTerm* all = Chain(s, clock);
    for (const LinearSequence& inter : s.intersects) {
      const SeqTerm* other = Chain(inter, clock);
      if (all == nullptr || other == nullptr) return nullptr;
      all = terms.Make(Kind::kIntersect, {all, other});
    }
    return all;
  }

  const SeqTerm* Chain(const LinearSequence& s, int clock) {
    std::vector<bool> used(s.throughouts.size(), false);
    Part part = Range(s, 0, s.operands.size() - 1, clock, used);
    if (part.term == nullptr) return nullptr;
    const SeqCycleDelay& lead = s.delays[0];
    return terms.Wait(lead.min - part.lead, Shorter(lead.max, part.lead),
                      part.term, terms.FirstClock(part.term));
  }

  static uint32_t Shorter(uint32_t bound, uint32_t by) {
    return bound == kUnbounded ? kUnbounded : bound - by;
  }

  // §16.9.9: the throughout not yet read that begins at operand `i` and
  // spans the furthest within operand `j`; the count of throughouts where
  // none does.
  static size_t SpanAt(const LinearSequence& s, size_t i, size_t j,
                       const std::vector<bool>& used) {
    size_t span = s.throughouts.size();
    for (size_t k = 0; k < s.throughouts.size(); ++k) {
      const SeqThroughout& guard = s.throughouts[k];
      if (used[k] || guard.first != i || guard.last > j) continue;
      if (span == s.throughouts.size() ||
          guard.last > s.throughouts[span].last) {
        span = k;
      }
    }
    return span;
  }

  Part Range(const LinearSequence& s, size_t i, size_t j, int clock,
             std::vector<bool>& used) {
    Part head;
    size_t last = i;
    size_t span = SpanAt(s, i, j, used);
    if (span < s.throughouts.size()) {
      const SeqThroughout& guard = s.throughouts[span];
      used[span] = true;
      Part inner = Range(s, i, guard.last, clock, used);
      if (inner.term == nullptr) return {};
      int first = terms.FirstClock(inner.term);
      head.term =
          terms.Make(Kind::kThroughout,
                     {terms.Wait(guard.lead - inner.lead,
                                 guard.lead - inner.lead, inner.term, first)},
                     Read(guard.cond), 0, 0, 0, first);
      head.lead = guard.lead;
      last = guard.last;
    } else {
      head.term = Item(s, i, clock);
    }
    if (head.term == nullptr || last == j) return head;
    Part rest = Range(s, last + 1, j, clock, used);
    if (rest.term == nullptr) return {};
    const SeqCycleDelay& d = s.delays[last + 1];
    head.term = terms.Make(Kind::kThen, {head.term, rest.term}, nullptr,
                           d.min - rest.lead, Shorter(d.max, rest.lead));
    return head;
  }

  // §16.9.2: the operand at `i` under its repetition, a boolean or a nested
  // sequence, on the clock it names or `clock`; nullptr where it carries
  // match items other than an unrepeated operand of a chain with locals.
  const SeqTerm* Item(const LinearSequence& s, size_t i, int clock) {
    int own = ClockOf(OperandClock(s, i), clock);
    const SeqRepetition& rep = s.repetitions[i];
    const std::vector<SeqMatchAssign>& items = s.match_items[i];
    bool repeated = rep.kind != SeqRepetition::Kind::kNone;
    if (!items.empty() && (!assigns_locals || repeated)) return nullptr;
    const LinearSequence* nested = NestedOperand(s, i);
    if (rep.kind == SeqRepetition::Kind::kGoto ||
        rep.kind == SeqRepetition::Kind::kNonconsecutive) {
      if (nested != nullptr) return nullptr;
      uint8_t flags = rep.kind == SeqRepetition::Kind::kNonconsecutive
                          ? kNonconsecutive
                          : 0;
      return terms.Make(Kind::kGoto, {}, Read(s.operands[i]), rep.min, rep.max,
                        0, own, flags);
    }
    const SeqTerm* base =
        nested != nullptr ? Body(*nested, own) : Bool(s, i, own, items);
    if (base == nullptr || !repeated) return base;
    return terms.Make(Kind::kRepeat, {base, base}, nullptr, rep.min, rep.max);
  }

  const SeqTerm* Bool(const LinearSequence& s, size_t i, int clock,
                      const std::vector<SeqMatchAssign>& items) {
    SeqTerm term;
    term.kind = Kind::kBool;
    term.expr = Read(s.operands[i]);
    term.items = items.empty() ? nullptr : &items;
    term.clock = clock;
    return terms.Intern(std::move(term));
  }
};

const SeqTerm* SeqTerms::Begin(const ModuleItem* item, int clock,
                               const ObligationRewrite& rewrite,
                               const ClockNumbering& clocks,
                               std::vector<Expr*>& reads, int& clock_out) {
  auto seq = std::make_unique<LinearSequence>();
  if (!FlattenLinearSequence(item, ctx_, arena_, *seq)) return nullptr;
  bool has_locals = !seq->locals.empty();
  size_t composite = seq->alternatives.size() + seq->conjuncts.size() +
                     seq->intersects.size() + seq->nested.size() +
                     static_cast<size_t>(seq->first_match);
  if (has_locals && composite != 0) return nullptr;
  Builder builder{*this, rewrite, clocks, reads, has_locals};
  const SeqTerm* term = builder.Body(*seq, clock);
  if (term == nullptr) return nullptr;
  if (has_locals) {
    term = Bind(Locals(InitialLocals(seq->locals, ctx_, arena_), &seq->locals),
                term);
  }
  clock_out = builder.ClockOf(seq->clock_out, clock);
  sequences_.push_back(std::move(seq));
  return term;
}

}  // namespace delta
