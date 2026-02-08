#include "common/diagnostic.h"

#include <format>
#include <iostream>

namespace delta {

static const char* severity_label(DiagSeverity sev) {
  switch (sev) {
    case DiagSeverity::Note:
      return "note";
    case DiagSeverity::Warning:
      return "warning";
    case DiagSeverity::Error:
      return "error";
    case DiagSeverity::Fatal:
      return "fatal error";
  }
  return "unknown";
}

void DiagEngine::note(SourceLoc loc, std::string msg) {
  emit(DiagSeverity::Note, loc, std::move(msg));
}

void DiagEngine::warning(SourceLoc loc, std::string msg) {
  if (warnings_as_errors_) {
    emit(DiagSeverity::Error, loc, std::move(msg));
    return;
  }
  emit(DiagSeverity::Warning, loc, std::move(msg));
}

void DiagEngine::error(SourceLoc loc, std::string msg) {
  emit(DiagSeverity::Error, loc, std::move(msg));
}

void DiagEngine::fatal(SourceLoc loc, std::string msg) {
  emit(DiagSeverity::Fatal, loc, std::move(msg));
}

void DiagEngine::emit(DiagSeverity sev, SourceLoc loc, std::string msg) {
  if (sev == DiagSeverity::Error || sev == DiagSeverity::Fatal) {
    ++error_count_;
  } else if (sev == DiagSeverity::Warning) {
    ++warning_count_;
  }

  auto loc_str = src_mgr_.format_loc(loc);
  std::cerr << std::format("{}: {}: {}\n", loc_str, severity_label(sev), msg);

  auto line_text = src_mgr_.get_line_text(loc);
  if (!line_text.empty()) {
    std::cerr << "  " << line_text << "\n";
    if (loc.column > 0) {
      std::cerr << "  " << std::string(loc.column - 1, ' ') << "^\n";
    }
  }

  diags_.push_back({sev, loc, std::move(msg)});
}

}  // namespace delta
