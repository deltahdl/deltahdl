#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/assume_obligations.h"
#include "simulator/sequence_flatten.h"

namespace delta {

namespace {

using State = SeqObligationState;
using Phase = SeqObligationState::Phase;
using Literals = std::vector<std::pair<Expr*, bool>>;

constexpr uint32_t kUnbounded = SeqCycleDelay::kUnbounded;

// One tick later: the ticks before the operand counted down by one, an
// unbounded wait staying unbounded.
State Shifted(State s) {
  if (s.lo > 0) --s.lo;
  if (s.hi != kUnbounded) --s.hi;
  return s;
}

// The ways the attempts go at the current tick, each state followed through
// the operands it reads at this tick.
class Expander {
 public:
  explicit Expander(const LinearSequence& seq) : seq_(seq) {}

  void Visit(const State& s, const Literals& lits) {
    if (s.lo > 0 || s.hi > 0) Continue(Shifted(s), lits);
    if (s.lo == 0) Try(s, lits);
  }

  std::vector<SeqObligationPath> Take() { return std::move(paths_); }

 private:
  void Continue(const State& next, const Literals& lits) {
    paths_.push_back({lits, false, next});
  }

  // §16.9.2: the operand read at this tick, by its repetition: an
  // unrepeated or consecutive one at each tick of its run, a goto one at
  // each tick until it holds, and a nonconsecutive one likewise and then
  // through the ticks after its last match at which it does not hold.
  void Try(const State& s, const Literals& lits) {
    Expr* operand = seq_.operands[s.op];
    const SeqRepetition& rep = seq_.repetitions[s.op];
    Literals held = lits;
    held.emplace_back(operand, true);
    Literals missed = lits;
    missed.emplace_back(operand, false);
    if (s.phase == Phase::kTail) {
      Advance(s.op, missed);
      Continue({s.op, 0, 0, s.count, Phase::kTail}, missed);
      return;
    }
    if (rep.kind == SeqRepetition::Kind::kGoto ||
        rep.kind == SeqRepetition::Kind::kNonconsecutive) {
      Continue({s.op, 0, 0, s.count, Phase::kRun}, missed);
    }
    Hold(s, rep, held);
  }

  void Hold(const State& s, const SeqRepetition& rep, const Literals& held) {
    uint32_t count = s.count + 1;
    if (rep.max == kUnbounded || count < rep.max) {
      Continue({s.op, 0, 0, count, Phase::kRun}, held);
    }
    if (count < rep.min) return;
    Advance(s.op, held);
    if (rep.kind == SeqRepetition::Kind::kNonconsecutive) {
      Continue({s.op, 0, 0, count, Phase::kTail}, held);
    }
  }

  // The operand at `op` matched at this tick: the sequence matches where it
  // is the last, and goes on to the next operand after its delay otherwise.
  void Advance(uint32_t op, const Literals& lits) {
    uint32_t next = op + 1;
    if (next == seq_.operands.size()) {
      paths_.push_back({lits, true, {}});
      return;
    }
    const SeqCycleDelay& d = seq_.delays[next];
    Visit({next, d.min, d.max, 0, Phase::kRun}, lits);
  }

  const LinearSequence& seq_;
  std::vector<SeqObligationPath> paths_;
};

}  // namespace

SeqObligationState SeqObligationStart(const LinearSequence& seq) {
  const SeqCycleDelay& lead = seq.delays[0];
  return {0, lead.min, lead.max, 0, Phase::kRun};
}

std::vector<SeqObligationPath> SeqObligationPaths(
    const LinearSequence& seq, const std::vector<SeqObligationState>& states) {
  Expander expander(seq);
  for (const State& s : states) expander.Visit(s, {});
  return expander.Take();
}

}  // namespace delta
