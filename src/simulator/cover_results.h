#pragma once

#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

#include "simulator/cover_statement.h"

namespace delta {

struct ImmediateCoverResult {
  std::string scope;
  uint32_t line = 0;
  uint64_t evaluated = 0;
  uint64_t succeeded = 0;
};

class ImmediateCoverResults {
 public:
  void Record(std::string scope, uint32_t line, bool succeeded);

  const std::vector<ImmediateCoverResult>& Results() const { return results_; }

  uint64_t Evaluated() const;
  uint64_t Succeeded() const;

 private:
  std::vector<ImmediateCoverResult> results_;
};

void ReportImmediateCoverResults(const ImmediateCoverResults& results,
                                 std::ostream& os);

struct ConcurrentCoverResult {
  std::string scope;
  uint32_t line = 0;
  CoverStatementCategory category = CoverStatementCategory::kProperty;
  uint64_t attempted = 0;
  uint64_t succeeded = 0;
  uint64_t vacuous = 0;
  uint64_t matched = 0;
};

class ConcurrentCoverResults {
 public:
  ConcurrentCoverResult& Record(std::string scope, uint32_t line,
                                CoverStatementCategory category);

  const std::vector<ConcurrentCoverResult>& Results() const { return results_; }

 private:
  std::vector<ConcurrentCoverResult> results_;
};

void ReportConcurrentCoverResults(const ConcurrentCoverResults& results,
                                  std::ostream& os);

}  // namespace delta
