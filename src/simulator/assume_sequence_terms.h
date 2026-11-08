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

using ObligationRewrite = std::function<Expr*(Expr*)>;

using ClockNumbering = std::function<int(const std::vector<EventExpr>&)>;

struct ObligationScope {
  ObligationRewrite rewrite;
  ClockNumbering clocks;
  const ObligationScope* base = nullptr;
};

struct SeqTermShape {
  Expr* expr = nullptr;
  uint32_t lo = 0;
  uint32_t hi = 0;
  uint32_t count = 0;
  int clock = 0;
  uint8_t flags = 0;
};

int NumberClock(const std::vector<EventExpr>& clock, int inherited,
                const ObligationRewrite& rewrite, const ClockNumbering& clocks);

class ConditionBuilder {
 public:
  explicit ConditionBuilder(Arena& arena);

  Expr* Always() const { return always_; }
  Expr* Never() const { return never_; }
  Expr* Not(Expr* a);
  Expr* And(Expr* a, Expr* b);
  Expr* Or(Expr* a, Expr* b);
  Expr* Join(Expr* a, Expr* b, bool conjunction);
  Expr* AllOf(const std::vector<std::pair<Expr*, bool>>& literals);

 private:
  Arena& arena_;
  Expr* always_ = nullptr;
  Expr* never_ = nullptr;
};

struct SeqTerm;
enum class SeqTermKind : uint8_t;

struct LocalValues {
  const std::vector<SeqLocalDecl>* decls = nullptr;
  std::vector<Logic4Vec> values;
  ActualsByFormal references;
};

void PerformMatchItems(
    const std::vector<const std::vector<SeqMatchAssign>*>& items,
    LocalValues& locals, SimContext& ctx, Arena& arena);

struct SeqWay {
  std::vector<std::pair<Expr*, bool>> literals;
  const SeqTerm* next = nullptr;
  std::vector<const std::vector<SeqMatchAssign>*> items;
  const LocalValues* locals = nullptr;
};

class SeqTerms {
 public:
  SeqTerms(SimContext& ctx, Arena& arena, ConditionBuilder& conditions);
  ~SeqTerms();
  SeqTerms(const SeqTerms&) = delete;
  SeqTerms& operator=(const SeqTerms&) = delete;

  const SeqTerm* Begin(const ModuleItem* item, int clock,
                       const ObligationScope& scope, std::vector<Expr*>& reads,
                       int& clock_out);

  const std::vector<SeqWay>& Ways(const SeqTerm* term, uint32_t ticked,
                                  bool anchor);

  const SeqTerm* Take(const SeqWay& way);

  const LocalValues* Locals(std::vector<Logic4Vec> values,
                            const std::vector<SeqLocalDecl>* decls);

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
  std::map<std::string_view, Variable*> local_vars_;
};

}  // namespace delta
