#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"

using namespace delta;

// Fails the running case over a source that drew an error the case never read,
// listing each error `diags` holds and then quoting `source`, so that the
// failure names the input rather than the harness. `remedy` says what the case
// had to read to take the rejection into account.
inline void ReportUnreadErrors(const std::vector<Diagnostic>& diags,
                               std::string_view remedy,
                               std::string_view source) {
  testing::Message report;
  report << "the source drew an error the case never read, so whatever it "
            "asserted was absent may be absent because nothing was "
            "compiled; "
         << remedy << ":\n";
  for (const auto& d : diags) {
    if (d.severity != DiagSeverity::kError) continue;
    report << "  line " << d.loc.line << ": " << d.message << "\n";
  }
  ADD_FAILURE() << report << source;
}

// Whether the source a fixture compiled drew an error, and whether the case it
// was handed to ever looked.
//
// A source deltahdl rejected produces the same absences a rule under test
// produces -- no instance, no binding, no second diagnostic -- so a case
// asserting that something does not appear holds whether its rule works, works
// backwards, or was never written, and it is reported as passing for as long as
// it stands. A case that has read the diagnostics has taken the rejection into
// account, whatever it concludes from them. A case that never read them passed
// on input that never compiled, and the destructor reports that, the end of the
// fixture's life being the last moment anybody could still have looked.
//
// The read is counted on the engine, DiagEngine::ReadCount, because a case
// reaches the diagnostics through the engine as often as through this answer:
// counting reads of has_errors alone once called hundreds of cases unread that
// had asked f.diag.HasErrors(). A fixture queries the engine itself while it
// compiles, so the reads that count toward the source it hands over are the
// ones after Record. An error reported after that, by a run of the design or by
// a source the case compiled on the engine itself, is read once any query of
// the engine follows it, which DiagEngine::HasUnreadError answers.
//
// A fixture declares its Diagnosed after its DiagEngine, so the engine is
// constructed first and destroyed last.
class Diagnosed {
 public:
  explicit Diagnosed(const DiagEngine& diag) : diag_(&diag) {}

  // A move carries the obligation to the new object and excuses the old, so a
  // fixture returned by value is reported once. The engine the new object
  // reads is the old fixture's, so a fixture returned by value relies on the
  // return being elided, as the reference DiagEngine keeps to its
  // SourceManager already does.
  Diagnosed(Diagnosed&& other) noexcept
      : diag_(other.diag_),
        errors_(other.errors_),
        reads_at_handover_(other.reads_at_handover_),
        asked_(other.asked_),
        excused_(other.excused_),
        source_(std::move(other.source_)) {
    other.excused_ = true;
  }
  Diagnosed(const Diagnosed&) = delete;
  Diagnosed& operator=(const Diagnosed&) = delete;
  Diagnosed& operator=(Diagnosed&&) = delete;

  ~Diagnosed() {
    if (excused_) return;
    bool handover_unread =
        errors_ && !asked_ && diag_->ReadCount() == reads_at_handover_;
    if (!handover_unread && !diag_->HasUnreadError()) return;
    ReportUnreadErrors(diag_->Diagnostics(),
                       "read has_errors or the engine's diagnostics after the "
                       "source is compiled",
                       source_);
  }

  // Marks the handover of `source`: the engine's answer as it stands, and the
  // reads the engine has had so far, all of them the fixture's own. The report
  // quotes `source`, so that a failure names the input rather than the harness.
  void Record(std::string_view source) {
    errors_ = diag_->HasErrors();
    reads_at_handover_ = diag_->ReadCount();
    asked_ = false;
    source_ = source;
  }

  // The same, for a caller that compiled the source itself and has only the
  // answer to hand.
  Diagnosed& operator=(bool errors) {
    errors_ = errors;
    reads_at_handover_ = diag_->ReadCount();
    asked_ = false;
    source_.clear();
    return *this;
  }

  // For a fixture that has already failed the case over the source it was
  // handed, where a second report would only repeat the first.
  void Excuse() { excused_ = true; }

  // Asking. Every shape a case reads this in -- EXPECT_TRUE, EXPECT_FALSE, an
  // `if`, a `!`, a `||` -- arrives here, which is why the obligation is
  // discharged here rather than at any one of them.
  operator bool() const {
    asked_ = true;
    return errors_;
  }

 private:
  const DiagEngine* diag_;
  bool errors_ = false;
  uint32_t reads_at_handover_ = 0;
  mutable bool asked_ = false;
  bool excused_ = false;
  std::string source_;
};
