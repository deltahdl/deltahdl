#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

namespace delta {

class Subclause {
 public:
  explicit constexpr Subclause(std::string_view text) : text_(text) {}

  static constexpr Subclause None() { return Subclause(std::string_view()); }

  constexpr std::string_view Text() const { return text_; }

 private:
  std::string_view text_;
};

enum class DiagSeverity : uint8_t {
  kWarning,
  kError,
};

struct Diagnostic {
  DiagSeverity severity = DiagSeverity::kError;
  SourceLoc loc;
  std::string message;
  std::string subclause;
};

class DiagEngine {
 public:
  explicit DiagEngine(const SourceManager& src_mgr) : src_mgr_(src_mgr) {}

  void Warning(SourceLoc loc, std::string msg, Subclause subclause);
  void Error(SourceLoc loc, std::string msg, Subclause subclause);
  void ErrorOnce(SourceLoc loc, std::string msg, Subclause subclause);

  bool HasErrors() const {
    NoteRead();
    return error_count_ > 0;
  }
  uint32_t ErrorCount() const {
    NoteRead();
    return error_count_;
  }
  uint32_t WarningCount() const {
    NoteRead();
    return warning_count_;
  }

  const std::vector<Diagnostic>& Diagnostics() const {
    NoteRead();
    return diags_;
  }

  uint32_t ReadCount() const { return read_count_; }
  bool HasUnreadError() const { return has_unread_error_; }

  const SourceManager& Sources() const { return src_mgr_; }

  void SetWarningsAsErrors(bool val) { warnings_as_errors_ = val; }

  void PushSuppress() { ++suppress_depth_; }
  void PopSuppress() { --suppress_depth_; }
  uint32_t SuppressedErrorCount() const {
    NoteRead();
    return suppressed_error_count_;
  }
  SourceLoc LastSuppressedErrorLoc() const {
    NoteRead();
    return last_suppressed_error_loc_;
  }

  void SetQuiet(bool val) { quiet_ = val; }

 private:
  void Emit(DiagSeverity sev, SourceLoc loc, std::string msg,
            Subclause subclause);
  void NoteRead() const {
    ++read_count_;
    has_unread_error_ = false;
  }

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  mutable uint32_t read_count_ = 0;
  mutable bool has_unread_error_ = false;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
  uint32_t suppress_depth_ = 0;
  uint32_t suppressed_error_count_ = 0;
  SourceLoc last_suppressed_error_loc_;
  bool quiet_ = false;
};

}  // namespace delta
