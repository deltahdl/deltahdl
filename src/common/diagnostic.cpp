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

void DiagEngine::Warning(SourceLoc loc, std::string msg) {
  if (warnings_as_errors_) {
    Emit(DiagSeverity::kError, loc, std::move(msg));
    return;
  }
  Emit(DiagSeverity::kWarning, loc, std::move(msg));
}

void DiagEngine::Error(SourceLoc loc, std::string msg) {
  Emit(DiagSeverity::kError, loc, std::move(msg));
}

void DiagEngine::Emit(DiagSeverity sev, SourceLoc loc, std::string msg) {
  if (sev == DiagSeverity::kError || sev == DiagSeverity::kFatal) {
    ++error_count_;
  } else if (sev == DiagSeverity::kWarning) {
    ++warning_count_;
  }

  auto loc_str = src_mgr_.FormatLoc(loc);
  std::cerr << std::format("{}: {}: {}\n", loc_str, SeverityLabel(sev), msg);

  auto line_text = src_mgr_.GetLineText(loc);
  if (!line_text.empty()) {
    std::cerr << "  " << line_text << "\n";
    if (loc.column > 0) {
      std::cerr << "  " << std::string(loc.column - 1, ' ') << "^\n";
    }
  }

  diags_.push_back({sev, loc, std::move(msg)});
}

}  // namespace delta
