#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

namespace delta {

// The subclause of IEEE 1800-2023 whose rule a report enforces. §1.5 organizes
// the standard into clauses and puts subclauses within each clause to discuss
// individual constructs and concepts, and it is a subclause that states the
// rule a report enforces: "5.7.1", not "5". A type rather than a bare string so
// that a report cannot be written without saying which of the three cases below
// it is in.
class Subclause {
 public:
  explicit constexpr Subclause(std::string_view text) : text_(text) {}

  // The report enforces no rule of the standard. An internal limit and a file
  // that cannot be opened are reports of this kind: they state a fact about
  // the run rather than a breach of the standard.
  static constexpr Subclause None() { return Subclause(std::string_view()); }

  // Nobody has yet read this site against the standard. No site carries this
  // any more: #2975 through #2987 and #2966 read every one of them, and the
  // assert-no-unread-subclause job in .github/workflows/deltahdl.yml fails on
  // a use of it anywhere under src/. It is kept as the word a reviewer greps
  // for, and a new report says None() where it enforces no rule of the
  // standard rather than saying this.
  static constexpr Subclause Unread() { return Subclause(std::string_view()); }

  constexpr std::string_view Text() const { return text_; }

 private:
  std::string_view text_;
};

// One value per entry point DiagEngine declares. A severity earns an
// enumerator when a caller needs it, together with the entry point that
// produces it: kWarning for DiagEngine::Warning, kError for
// DiagEngine::Error, and the Diagnostics.EverySeverityHasAProducer test over
// both.
enum class DiagSeverity : uint8_t {
  kWarning,
  kError,
};

struct Diagnostic {
  DiagSeverity severity = DiagSeverity::kError;
  SourceLoc loc;
  std::string message;
  // The subclause of IEEE 1800-2023 stating the rule this reports, written as
  // the standard numbers it: "11.4.14", "16.12.17". Held as text because the
  // numbering is not arithmetic and a subclause has as many components as the
  // standard gives it. Empty when the report states no rule of the standard,
  // as an internal limit does.
  std::string subclause;
};

class DiagEngine {
 public:
  explicit DiagEngine(const SourceManager& src_mgr) : src_mgr_(src_mgr) {}

  // The two reports, each naming the subclause of IEEE 1800-2023 the reported
  // rule comes from. Give the subclause as the standard numbers it and without
  // a section sign, Subclause("11.4.14") rather than Subclause("§11.4.14"): the
  // sign is added when the diagnostic is written out. A caller that reads the
  // record back then learns which rule was enforced without matching the
  // wording of the message, so rewording a message costs nothing.
  //
  // The subclause is required and there is no form that omits it, so a report
  // cannot say nothing about which rule it enforces by saying nothing. A
  // report that enforces no rule of the standard says so with
  // Subclause::None(), which is the only answer left for a report that names
  // no subclause: Subclause::Unread() is rejected by CI.
  void Warning(SourceLoc loc, std::string msg, Subclause subclause);
  void Error(SourceLoc loc, std::string msg, Subclause subclause);

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
            Subclause subclause);

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
  uint32_t suppress_depth_ = 0;
};

}  // namespace delta
