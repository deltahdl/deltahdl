#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"

using namespace delta;

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

class Diagnosed {
 public:
  explicit Diagnosed(const DiagEngine& diag) : diag_(&diag) {}

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

  void Record(std::string_view source) {
    errors_ = diag_->HasErrors();
    reads_at_handover_ = diag_->ReadCount();
    asked_ = false;
    source_ = source;
  }

  Diagnosed& operator=(bool errors) {
    errors_ = errors;
    reads_at_handover_ = diag_->ReadCount();
    asked_ = false;
    source_.clear();
    return *this;
  }

  void Excuse() { excused_ = true; }

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
