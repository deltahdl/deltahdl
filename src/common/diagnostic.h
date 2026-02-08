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
};

class DiagEngine {
 public:
  explicit DiagEngine(const SourceManager& src_mgr) : src_mgr_(src_mgr) {}

  void Warning(SourceLoc loc, std::string msg);
  void Error(SourceLoc loc, std::string msg);

  bool HasErrors() const { return error_count_ > 0; }
  uint32_t WarningCount() const { return warning_count_; }

  void SetWarningsAsErrors(bool val) { warnings_as_errors_ = val; }

 private:
  void Emit(DiagSeverity sev, SourceLoc loc, std::string msg);

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
};

}  // namespace delta
