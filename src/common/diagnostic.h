#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/source_mgr.h"

namespace delta {

enum class DiagSeverity : uint8_t {
  Note,
  Warning,
  Error,
  Fatal,
};

struct Diagnostic {
  DiagSeverity severity = DiagSeverity::Error;
  SourceLoc loc;
  std::string message;
};

class DiagEngine {
 public:
  explicit DiagEngine(const SourceManager& src_mgr) : src_mgr_(src_mgr) {}

  void note(SourceLoc loc, std::string msg);
  void warning(SourceLoc loc, std::string msg);
  void error(SourceLoc loc, std::string msg);
  void fatal(SourceLoc loc, std::string msg);

  uint32_t error_count() const { return error_count_; }
  uint32_t warning_count() const { return warning_count_; }
  bool has_errors() const { return error_count_ > 0; }

  const std::vector<Diagnostic>& diagnostics() const { return diags_; }

  void set_warnings_as_errors(bool val) { warnings_as_errors_ = val; }

 private:
  void emit(DiagSeverity sev, SourceLoc loc, std::string msg);

  const SourceManager& src_mgr_;
  std::vector<Diagnostic> diags_;
  uint32_t error_count_ = 0;
  uint32_t warning_count_ = 0;
  bool warnings_as_errors_ = false;
};

}  // namespace delta
