#include "simulator/cover_results.h"

#include <cstdint>
#include <ostream>
#include <string>
#include <utility>

#include "simulator/cover_statement.h"

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

ConcurrentCoverResult& ConcurrentCoverResults::Record(
    std::string scope, uint32_t line, CoverStatementCategory category) {
  for (ConcurrentCoverResult& result : results_) {
    if (result.line == line && result.scope == scope) return result;
  }
  results_.push_back({std::move(scope), line, category});
  return results_.back();
}

void ReportConcurrentCoverResults(const ConcurrentCoverResults& results,
                                  std::ostream& os) {
  // The line names the statement as an immediate cover's does, its category
  // first, and carries the counts §16.14.3 lists for the category, the
  // attempts before what they yielded.
  for (const ConcurrentCoverResult& result : results.Results()) {
    bool sequence = result.category == CoverStatementCategory::kSequence;
    os << "cover " << (sequence ? "sequence " : "property ") << result.scope
       << " (line " << result.line << "): attempted " << result.attempted;
    if (sequence) {
      os << ", matched " << result.matched << "\n";
    } else {
      os << ", succeeded " << result.succeeded << ", succeeded vacuously "
         << result.vacuous << "\n";
    }
  }
}

}  // namespace delta
