#pragma once

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

#include "simulator/cover_statement.h"

namespace delta {

// §16.3: the results of coverage for an immediate cover statement contain the
// number of times it was evaluated and the number of times it succeeded. One
// record stands for one statement in one scope, named as %m names the scope
// (§21.2.1.5) with the statement's source line beside it, since a module
// instantiated twice runs the one statement in two scopes and each is its own
// coverage goal.
struct ImmediateCoverResult {
  std::string scope;
  uint32_t line = 0;
  uint64_t evaluated = 0;
  uint64_t succeeded = 0;
};

// The coverage information §16.3 has a tool collect for its immediate cover
// statements, in the order the statements were first evaluated.
class ImmediateCoverResults {
 public:
  // Counts one evaluation of the statement at `line` in `scope`, succeeded
  // or not, opening the statement's record on its first evaluation.
  void Record(std::string scope, uint32_t line, bool succeeded);

  const std::vector<ImmediateCoverResult>& Results() const { return results_; }

  // The two counts summed over every statement.
  uint64_t Evaluated() const;
  uint64_t Succeeded() const;

 private:
  std::vector<ImmediateCoverResult> results_;
};

// §16.3: a tool reports the results of coverage for its immediate cover
// statements at the end of simulation. One line per record, in the order the
// statements were first evaluated, and nothing when the design holds none.
void ReportImmediateCoverResults(const ImmediateCoverResults& results,
                                 std::ostream& os);

// §16.14.3: the results of coverage for one concurrent cover statement in one
// scope, named as an immediate cover's record is, the scope being the
// statement's own where it carries a label, as %m in its pass statement names
// it (§21.2.1.5). A cover property's results are the attempts, the disabled
// ones among them, the successes, at most one per attempt and none disabled,
// and the successes because of vacuity, which are counted apart from the
// successes; a cover sequence's are the attempts and the matches, every match
// of an attempt counted with multiplicity.
struct ConcurrentCoverResult {
  std::string scope;
  uint32_t line = 0;
  CoverStatementCategory category = CoverStatementCategory::kProperty;
  uint64_t attempted = 0;
  uint64_t succeeded = 0;
  uint64_t vacuous = 0;
  uint64_t matched = 0;
};

// The coverage information §16.14.3 has a tool collect for its concurrent
// cover statements, in the order the statements first attempted.
class ConcurrentCoverResults {
 public:
  // The record of the statement at `line` in `scope`, opened on its first
  // attempt with `category`, for the caller to count on.
  ConcurrentCoverResult& Record(std::string scope, uint32_t line,
                                CoverStatementCategory category);

  const std::vector<ConcurrentCoverResult>& Results() const { return results_; }

 private:
  std::vector<ConcurrentCoverResult> results_;
};

// §16.14.3: a tool reports the results of coverage at the end of simulation.
// One line per record, in the order the statements first attempted, a cover
// property's carrying its three counts and a cover sequence's its two, and
// nothing when the design holds no concurrent cover.
void ReportConcurrentCoverResults(const ConcurrentCoverResults& results,
                                  std::ostream& os);

}  // namespace delta
