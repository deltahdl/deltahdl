#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/sequence_flatten.h"

namespace delta {

class Arena;
class SimContext;
struct Variable;

// Rewrites an expression an assumption reads into the terms of the checker
// whose free variables it constrains: a child checker's formal into its
// actual (§17.7.2).
using ObligationRewrite = std::function<Expr*(Expr*)>;

// Numbers a clocking event among those an assumption is evaluated on, the
// leading clock 0 (§16.13).
using ClockNumbering = std::function<int(const std::vector<EventExpr>&)>;

// The terms an assumption is read in: the rewrite of its expressions into
// the terms of the checker whose free variables it constrains, and the
// numbering of its clocks; `base`, where it is set, the terms the
// assumption itself is read in, of which these are a named property's
// body's (§16.12.17).
struct ObligationScope {
  ObligationRewrite rewrite;
  ClockNumbering clocks;
  const ObligationScope* base = nullptr;
};

// The fields of a sequence term other than its kind and operands.
struct SeqTermShape {
  Expr* expr = nullptr;
  uint32_t lo = 0;
  uint32_t hi = 0;
  uint32_t count = 0;
  int clock = 0;
  uint8_t flags = 0;
};

// §16.13: the number of `clock`, its expressions rewritten by `rewrite`,
// among the clocks `clocks` numbers; `inherited` where it is empty, the
// clock flowing to it.
int NumberClock(const std::vector<EventExpr>& clock, int inherited,
                const ObligationRewrite& rewrite, const ClockNumbering& clocks);

// Conditions over the values a time step reads, built from expressions with
// the conditions met under any values and under none folded away.
class ConditionBuilder {
 public:
  explicit ConditionBuilder(Arena& arena);

  Expr* Always() const { return always_; }
  Expr* Never() const { return never_; }
  Expr* Not(Expr* a);
  Expr* And(Expr* a, Expr* b);
  Expr* Or(Expr* a, Expr* b);
  // `a && b`, or `a || b` where `conjunction` is unset.
  Expr* Join(Expr* a, Expr* b, bool conjunction);
  // The conjunction of `literals`, each expression read as its truth or,
  // where it is paired with false, its negation.
  Expr* AllOf(const std::vector<std::pair<Expr*, bool>>& literals);

 private:
  Arena& arena_;
  Expr* always_ = nullptr;
  Expr* never_ = nullptr;
};

// §17.7.2: what one attempt of a sequence still has to match, from the tick
// it is read at on: a residual of §16.7 to §16.10's operators over boolean
// operands, each operand on the clock numbered `clock` (§16.13.1). Terms are
// shared, so that attempts owing the same are one term.
struct SeqTerm;
enum class SeqTermKind : uint8_t;

// §16.10: the values of the local variables `decls` declares for one
// attempt, each with an identifier under the local's name, which the
// expressions reading the locals read in their place: it names a variable
// of the local's declared type holding the value (SeqTerms::Locals), which
// SeqTerms::BindLocalsOf binds where such an expression is evaluated.
struct LocalValues {
  const std::vector<SeqLocalDecl>* decls = nullptr;
  std::vector<Logic4Vec> values;
  ActualsByFormal references;
};

// §16.10: the match items of each of `items` performed in turn on
// `locals`, `lvar = rhs` or `lvar op= rhs` assigning the local `lvar`
// declares at its width; an item naming no local of `decls`, a subroutine
// call (§16.11) among them, assigns none.
void PerformMatchItems(
    const std::vector<const std::vector<SeqMatchAssign>*>& items,
    LocalValues& locals, SimContext& ctx, Arena& arena);

// One way an attempt goes at a tick: the expressions it reads there, each
// with the truth it needs; the term it goes on in from the next tick,
// nullptr where it matches at this tick; and the match items of the
// operands it matched, performed on the attempt's locals `locals`.
struct SeqWay {
  std::vector<std::pair<Expr*, bool>> literals;
  const SeqTerm* next = nullptr;
  std::vector<const std::vector<SeqMatchAssign>*> items;
  const LocalValues* locals = nullptr;
};

// §17.7.2: the terms of the sequences an assume set's assumptions read.
class SeqTerms {
 public:
  SeqTerms(SimContext& ctx, Arena& arena, ConditionBuilder& conditions);
  ~SeqTerms();
  SeqTerms(const SeqTerms&) = delete;
  SeqTerms& operator=(const SeqTerms&) = delete;

  // The term an attempt of the sequence `item` begins in, read in `scope`,
  // its operands on `clock` where they name no clock of their own and each
  // expression it reads appended to `reads`; nullptr where the flattening
  // does not read it. `clock_out` is set to the number of the clock
  // flowing out of its end (§16.13.3).
  const SeqTerm* Begin(const ModuleItem* item, int clock,
                       const ObligationScope& scope, std::vector<Expr*>& reads,
                       int& clock_out);

  // The ways of the attempts in `term` at a tick, the clocks that ticked at
  // it a bit each in `ticked`; `anchor` where the tick is the one the term
  // was begun at, from which the delays before its operands count.
  const std::vector<SeqWay>& Ways(const SeqTerm* term, uint32_t ticked,
                                  bool anchor);

  // The term the way `way` goes on in, its match items performed on the
  // values read at the time step.
  const SeqTerm* Take(const SeqWay& way);

  // The values `values` of the locals `decls` declares, shared among the
  // attempts holding the same.
  const LocalValues* Locals(std::vector<Logic4Vec> values,
                            const std::vector<SeqLocalDecl>* decls);

  // §16.10: binds, in the innermost scope, the variable each identifier of
  // `e` names that stands for a local's value (LocalValues::references).
  void BindLocalsOf(const Expr* e);

 private:
  struct Builder;

  const SeqTerm* Intern(SeqTerm term);
  const SeqTerm* Make(SeqTermKind kind, std::vector<const SeqTerm*> operands,
                      const SeqTermShape& shape = {});
  const SeqTerm* PairedNext(SeqTermKind kind, const SeqTerm* a,
                            const SeqTerm* b);
  const SeqTerm* Wait(uint32_t lo, uint32_t hi, const SeqTerm* x, int clock);
  const SeqTerm* Bind(const LocalValues* locals, const SeqTerm* x);
  bool Nullable(const SeqTerm* term);
  int FirstClock(const SeqTerm* term);

  void Expand(const SeqTerm* term, uint32_t ticked, bool anchor,
              std::vector<SeqWay>& out);
  void ExpandWait(const SeqTerm* term, uint32_t ticked, bool anchor,
                  std::vector<SeqWay>& out);
  void ExpandThen(const SeqTerm* term, uint32_t ticked, bool anchor,
                  std::vector<SeqWay>& out);
  void ExpandPair(const SeqTerm* term, uint32_t ticked, bool anchor,
                  std::vector<SeqWay>& out);
  void ExpandThroughout(const SeqTerm* term, uint32_t ticked, bool anchor,
                        std::vector<SeqWay>& out);
  void ExpandFirstMatch(const SeqTerm* term, uint32_t ticked, bool anchor,
                        std::vector<SeqWay>& out);
  void ExpandRepeat(const SeqTerm* term, uint32_t ticked, bool anchor,
                    std::vector<SeqWay>& out);
  void ExpandGoto(const SeqTerm* term, std::vector<SeqWay>& out);
  void ExpandBind(const SeqTerm* term, uint32_t ticked, bool anchor,
                  std::vector<SeqWay>& out);
  Expr* UnderLocals(Expr* e, const LocalValues* locals);
  Expr* LocalReference(SeqLocalDecl decl, const Logic4Vec& value);

  SimContext& ctx_;
  Arena& arena_;
  ConditionBuilder& conditions_;
  std::map<std::string, std::unique_ptr<SeqTerm>> terms_;
  std::map<std::string, std::unique_ptr<LocalValues>> locals_;
  std::vector<std::unique_ptr<LinearSequence>> sequences_;
  std::vector<std::unique_ptr<std::vector<SeqLocalDecl>>> local_decls_;
  const SeqTerm* match_ = nullptr;
  // §16.10: the variables LocalReference stood up, by the names it gave them.
  std::map<std::string_view, Variable*> local_vars_;
};

}  // namespace delta
