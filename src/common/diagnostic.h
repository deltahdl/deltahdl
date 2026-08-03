#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

namespace delta {

enum class DiagSeverity : uint8_t {
  kNote,
  kWarning,
  kError,
  kFatal,
};

struct Diagnostic {
  DiagSeverity severity = DiagSeverity::kError;
  SourceLoc loc;
  std::string message;
  // The clause of IEEE 1800-2023 stating the rule this reports, written as the
  // standard numbers it: "11.4.14", "16.12.17". Held as text because clause
  // numbering is not arithmetic and a subclause has as many components as the
  // standard gives it. Empty when the report states no rule of the standard,
  // as an internal limit does.
  std::string clause;
};

class DiagEngine {
 public:
  explicit DiagEngine(const SourceManager& src_mgr) : src_mgr_(src_mgr) {}

  void Warning(SourceLoc loc, std::string msg);
  void Error(SourceLoc loc, std::string msg);

  // The same two reports, naming the clause of IEEE 1800-2023 the reported
  // rule comes from. Give the clause as the standard numbers it and without a
  // section sign, "11.4.14" rather than "§11.4.14": the sign is added when the
  // diagnostic is written out. A caller that reads the record back then learns
  // which rule was enforced without matching the wording of the message, so
  // rewording a message costs nothing.
  void Warning(SourceLoc loc, std::string msg, std::string clause);
  void Error(SourceLoc loc, std::string msg, std::string clause);

  bool HasErrors() const { return error_count_ > 0; }
  // How many errors have been reported so far. A caller that runs one step of
  // a longer job on a shared engine reads this before and after the step to
  // learn whether that step failed, which HasErrors() cannot tell it once an
  // earlier step has already reported something.
  uint32_t ErrorCount() const { return error_count_; }
  uint32_t WarningCount() const { return warning_count_; }

  // The diagnostics reported so far, in the order they were reported. A caller
  // asserting that a run failed for one reason rather than another reads the
  // message and the location here, which the counts above cannot distinguish:
  // every cause of failure adds one to the same count.
  const std::vector<Diagnostic>& Diagnostics() const { return diags_; }

  void SetWarningsAsErrors(bool val) { warnings_as_errors_ = val; }

  // Temporarily suppress every diagnostic (and its count) while a speculative
  // parse runs, so a trial parse whose result is discarded never reports
  // errors. Calls nest; diagnostics resume once the outermost suppression is
  // released.
  void PushSuppress() { ++suppress_depth_; }
  void PopSuppress() {
    if (suppress_depth_ > 0) --suppress_depth_;
  }

 private:
  void Emit(DiagSeverity sev, SourceLoc loc, std::string msg,
            std::string clause);

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
  uint32_t suppress_depth_ = 0;
};

}  // namespace delta
