#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

namespace delta {

// The clause of IEEE 1800-2023 whose rule a report enforces. A type rather
// than a bare string so that a report cannot be written without saying which
// of the three cases below it is in.
class Clause {
 public:
  explicit constexpr Clause(std::string_view text) : text_(text) {}

  // The report enforces no rule of the standard. An internal limit and a file
  // that cannot be opened are reports of this kind: they state a fact about
  // the run rather than a breach of the standard.
  static constexpr Clause None() { return Clause(std::string_view()); }

  // Nobody has yet read this site against the standard. Every site carrying
  // this is work owed by #2975 through #2987 and #2966, and the value is
  // deleted from the tree when the last of them lands. It is the same value as
  // None() to everything that runs, and a different word to everything that
  // reads the source, which is where the two have to be told apart.
  static constexpr Clause Unread() { return Clause(std::string_view()); }

  constexpr std::string_view Text() const { return text_; }

 private:
  std::string_view text_;
};

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

  // The two reports, each naming the clause of IEEE 1800-2023 the reported
  // rule comes from. Give the clause as the standard numbers it and without a
  // section sign, Clause("11.4.14") rather than Clause("§11.4.14"): the sign
  // is added when the diagnostic is written out. A caller that reads the
  // record back then learns which rule was enforced without matching the
  // wording of the message, so rewording a message costs nothing.
  //
  // The clause is required and there is no form that omits it, so a report
  // cannot say nothing about which rule it enforces by saying nothing. A
  // report that enforces no rule of the standard says so with Clause::None(),
  // and one nobody has yet read against the standard says so with
  // Clause::Unread().
  void Warning(SourceLoc loc, std::string msg, Clause clause);
  void Error(SourceLoc loc, std::string msg, Clause clause);

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
  void Emit(DiagSeverity sev, SourceLoc loc, std::string msg, Clause clause);

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
  uint32_t suppress_depth_ = 0;
};

}  // namespace delta
