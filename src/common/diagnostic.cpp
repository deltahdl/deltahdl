#include "common/diagnostic.h"

#include <format>
#include <iostream>

namespace delta {

static const char* SeverityLabel(DiagSeverity sev) {
  switch (sev) {
    case DiagSeverity::kNote:
      return "note";
    case DiagSeverity::kWarning:
      return "warning";
    case DiagSeverity::kError:
      return "error";
    case DiagSeverity::kFatal:
      return "fatal error";
  }
  return "unknown";
}

void DiagEngine::Warning(SourceLoc loc, std::string msg, Subclause subclause) {
  if (warnings_as_errors_) {
    Emit(DiagSeverity::kError, loc, std::move(msg), subclause);
    return;
  }
  Emit(DiagSeverity::kWarning, loc, std::move(msg), subclause);
}

void DiagEngine::Error(SourceLoc loc, std::string msg, Subclause subclause) {
  Emit(DiagSeverity::kError, loc, std::move(msg), subclause);
}

void DiagEngine::Emit(DiagSeverity sev, SourceLoc loc, std::string msg,
                      Subclause subclause) {
  if (suppress_depth_ > 0) return;
  if (sev == DiagSeverity::kError || sev == DiagSeverity::kFatal) {
    ++error_count_;
  } else if (sev == DiagSeverity::kWarning) {
    ++warning_count_;
  }

  // A named subclause is appended to the sentence in the form the messages that
  // spell it out already use, so a report that moved the subclause out of its
  // sentence reads to a user exactly as it did before.
  auto loc_str = src_mgr_.FormatLoc(loc);
  auto subclause_str = subclause.Text().empty()
                           ? std::string()
                           : std::format(" (§{})", subclause.Text());
  std::cerr << std::format("{}: {}: {}{}\n", loc_str, SeverityLabel(sev), msg,
                           subclause_str);

  auto line_text = src_mgr_.GetLineText(loc);
  if (!line_text.empty()) {
    std::cerr << "  " << line_text << "\n";
    if (loc.column > 0) {
      std::cerr << "  " << std::string(loc.column - 1, ' ') << "^\n";
    }
  }

  diags_.push_back({sev, loc, std::move(msg), std::string(subclause.Text())});
}

}  // namespace delta
