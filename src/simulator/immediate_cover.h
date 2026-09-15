#pragma once

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

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

}  // namespace delta
