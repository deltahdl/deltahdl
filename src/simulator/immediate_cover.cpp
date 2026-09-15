#include "simulator/immediate_cover.h"

#include <cstdint>
#include <ostream>
#include <string>
#include <utility>

namespace delta {

void ImmediateCoverResults::Record(std::string scope, uint32_t line,
                                   bool succeeded) {
  for (ImmediateCoverResult& result : results_) {
    if (result.line == line && result.scope == scope) {
      ++result.evaluated;
      if (succeeded) ++result.succeeded;
      return;
    }
  }
  results_.push_back({std::move(scope), line, 1, succeeded ? 1u : 0u});
}

uint64_t ImmediateCoverResults::Evaluated() const {
  uint64_t total = 0;
  for (const ImmediateCoverResult& result : results_) total += result.evaluated;
  return total;
}

uint64_t ImmediateCoverResults::Succeeded() const {
  uint64_t total = 0;
  for (const ImmediateCoverResult& result : results_) total += result.succeeded;
  return total;
}

void ReportImmediateCoverResults(const ImmediateCoverResults& results,
                                 std::ostream& os) {
  // The line names the statement as a severity task's header names its call
  // site (§20.10), the scope and then the source line, and carries the two
  // counts §16.3 lists, evaluated before succeeded.
  for (const ImmediateCoverResult& result : results.Results()) {
    os << "cover " << result.scope << " (line " << result.line
       << "): evaluated " << result.evaluated << ", succeeded "
       << result.succeeded << "\n";
  }
}

}  // namespace delta
