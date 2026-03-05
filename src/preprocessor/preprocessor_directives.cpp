#include <cctype>
#include <fstream>

#include "preprocessor/preprocessor.h"

namespace delta {

static std::string_view TrimDirective(std::string_view s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front())))
    s.remove_prefix(1);
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back())))
    s.remove_suffix(1);
  return s;
}

// --- Timescale parsing ---

static bool ParseTimescaleComponent(std::string_view text, int& magnitude,
                                    TimeUnit& unit) {
  auto trimmed = TrimDirective(text);
  if (trimmed.empty()) return false;

  // Extract leading digits for magnitude.
  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) return false;

  int mag = 0;
  for (size_t j = 0; j < i; ++j) {
    mag = mag * 10 + (trimmed[j] - '0');
  }
  if (mag != 1 && mag != 10 && mag != 100) return false;
  magnitude = mag;

  auto unit_str = TrimDirective(trimmed.substr(i));
  return ParseTimeUnitStr(unit_str, unit);
}

void Preprocessor::HandleTimescale(std::string_view rest, SourceLoc loc) {
  // Format: `timescale unit_mag unit / prec_mag precision
  auto slash = rest.find('/');
  if (slash == std::string_view::npos) {
    diag_.Error(loc, "invalid `timescale format: missing '/'");
    return;
  }
  auto unit_part = rest.substr(0, slash);
  auto prec_part = rest.substr(slash + 1);

  TimeScale ts;
  if (!ParseTimescaleComponent(unit_part, ts.magnitude, ts.unit)) {
    diag_.Error(loc, "invalid `timescale unit");
    return;
  }
  if (!ParseTimescaleComponent(prec_part, ts.prec_magnitude, ts.precision)) {
    diag_.Error(loc, "invalid `timescale precision");
    return;
  }

  // §22.7: precision shall be at least as precise as the unit.
  if (static_cast<int>(ts.precision) > static_cast<int>(ts.unit)) {
    diag_.Error(loc,
                "`timescale precision is less precise than the time unit");
    return;
  }

  current_timescale_ = ts;
  if (!has_timescale_ ||
      static_cast<int>(ts.precision) < static_cast<int>(global_precision_)) {
    global_precision_ = ts.precision;
  }
  has_timescale_ = true;
}

// --- default_nettype / unconnected_drive ---

static bool ParseNetTypeName(std::string_view name, NetType& out) {
  if (name == "wire") {
    out = NetType::kWire;
  } else if (name == "tri") {
    out = NetType::kTri;
  } else if (name == "wand") {
    out = NetType::kWand;
  } else if (name == "triand") {
    out = NetType::kTriand;
  } else if (name == "wor") {
    out = NetType::kWor;
  } else if (name == "trior") {
    out = NetType::kTrior;
  } else if (name == "tri0") {
    out = NetType::kTri0;
  } else if (name == "tri1") {
    out = NetType::kTri1;
  } else if (name == "uwire") {
    out = NetType::kUwire;
  } else if (name == "trireg") {
    out = NetType::kTrireg;
  } else {
    return false;
  }
  return true;
}

void Preprocessor::HandleDefaultNettype(std::string_view rest, SourceLoc loc) {
  auto name = TrimDirective(rest);
  if (name == "none") {
    default_net_type_ = NetType::kNone;
    return;
  }
  NetType nt = NetType::kWire;
  if (!ParseNetTypeName(name, nt)) {
    diag_.Error(loc, "invalid net type '" + std::string(name) + "'");
    return;
  }
  default_net_type_ = nt;
}

void Preprocessor::HandleUnconnectedDrive(std::string_view rest,
                                          SourceLoc loc) {
  auto arg = TrimDirective(rest);
  if (arg == "pull0") {
    unconnected_drive_ = NetType::kTri0;
  } else if (arg == "pull1") {
    unconnected_drive_ = NetType::kTri1;
  } else {
    diag_.Error(
        loc, "invalid `unconnected_drive argument: '" + std::string(arg) + "'");
  }
}

void Preprocessor::HandleLine(std::string_view rest, SourceLoc loc) {
  // Format: number "filename" level  (§22.12)
  auto trimmed = TrimDirective(rest);
  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) {
    diag_.Error(loc, "invalid `line directive: missing or invalid line number");
    return;
  }
  uint32_t new_line = 0;
  for (size_t j = 0; j < i; ++j) {
    new_line = new_line * 10 + (trimmed[j] - '0');
  }

  // §22.12: number must be a positive integer (zero is not positive).
  if (new_line == 0) {
    diag_.Error(loc, "`line number must be a positive integer");
    return;
  }

  // Parse required filename (must be a string literal).
  auto after_num = TrimDirective(trimmed.substr(i));
  if (after_num.empty() || after_num[0] != '"') {
    diag_.Error(loc, "`line directive requires a quoted filename");
    return;
  }
  auto end_quote = after_num.find('"', 1);
  if (end_quote == std::string_view::npos) {
    diag_.Error(loc, "unterminated string in `line directive");
    return;
  }
  auto filename = after_num.substr(1, end_quote - 1);

  // Parse required level (must be 0, 1, or 2).
  auto after_file = TrimDirective(after_num.substr(end_quote + 1));
  if (after_file.empty() ||
      !std::isdigit(static_cast<unsigned char>(after_file[0]))) {
    diag_.Error(loc, "`line directive requires a level (0, 1, or 2)");
    return;
  }
  int level = after_file[0] - '0';
  if (level > 2) {
    diag_.Error(loc, "`line level must be 0, 1, or 2");
    return;
  }

  // §22.12: Only whitespace may appear after the level on the same line.
  auto after_level = TrimDirective(after_file.substr(1));
  if (!after_level.empty()) {
    diag_.Error(loc, "only whitespace may appear on the same line as `line");
    return;
  }

  line_offset_ = new_line;
  line_override_src_line_ = loc.line;
  has_line_override_ = true;
  line_file_override_ = std::string(filename);
}

std::string Preprocessor::ResolveInclude(std::string_view filename,
                                         const std::string& src_dir) {
  if (!filename.empty() && filename[0] == '/') {
    std::string path{filename};
    std::ifstream ifs(path);
    if (ifs.good()) return path;
  }
  // §22.4: try relative to source file directory first.
  if (!src_dir.empty()) {
    auto path = src_dir + "/" + std::string(filename);
    std::ifstream ifs(path);
    if (ifs.good()) return path;
  }
  for (const auto& dir : config_.include_dirs) {
    auto path = dir + "/" + std::string(filename);
    std::ifstream ifs(path);
    if (ifs.good()) {
      return path;
    }
  }
  return "";
}

void Preprocessor::HandleBeginKeywords(std::string_view rest, SourceLoc loc,
                                       std::string& output) {
  auto start = rest.find('"');
  auto end = rest.find('"', start + 1);
  if (start == std::string_view::npos || end == std::string_view::npos) {
    diag_.Error(loc, "expected quoted version string after `begin_keywords");
    return;
  }
  auto spec = rest.substr(start + 1, end - start - 1);
  auto version = ParseKeywordVersion(spec);
  if (!version) {
    diag_.Error(
        loc, "unrecognized version specifier: \"" + std::string(spec) + "\"");
    return;
  }
  keyword_version_stack_.push_back(*version);
  output += kKeywordMarker;
  output += static_cast<char>(static_cast<uint8_t>(*version));
  output += '\n';
}

void Preprocessor::HandleEndKeywords(SourceLoc loc, std::string& output) {
  if (keyword_version_stack_.empty()) {
    diag_.Error(loc, "`end_keywords without matching `begin_keywords");
    return;
  }
  keyword_version_stack_.pop_back();
  auto version = keyword_version_stack_.empty() ? KeywordVersion::kVer18002023
                                                : keyword_version_stack_.back();
  output += kKeywordMarker;
  output += static_cast<char>(static_cast<uint8_t>(version));
  output += '\n';
}

// --- Annex E: optional compiler directives ---

void Preprocessor::HandleDefaultDecayTime(std::string_view rest,
                                          SourceLoc loc) {
  auto arg = TrimDirective(rest);
  if (arg.empty()) {
    diag_.Error(loc, "`default_decay_time requires an argument");
    return;
  }
  if (arg == "infinite") {
    default_decay_time_infinite_ = true;
    default_decay_time_ = 0;
    default_decay_time_real_ = 0.0;
    return;
  }
  // Try parsing as integer or real constant.
  bool has_dot = arg.find('.') != std::string_view::npos;
  if (has_dot) {
    // Real constant.
    size_t i = 0;
    bool saw_dot = false;
    while (i < arg.size()) {
      if (arg[i] == '.' && !saw_dot) {
        saw_dot = true;
      } else if (!std::isdigit(static_cast<unsigned char>(arg[i]))) {
        diag_.Error(loc, "invalid `default_decay_time argument: '" +
                             std::string(arg) + "'");
        return;
      }
      ++i;
    }
    double val = 0.0;
    // Manual parse: integer part + fractional part.
    auto dot_pos = arg.find('.');
    auto int_part = arg.substr(0, dot_pos);
    auto frac_part = arg.substr(dot_pos + 1);
    for (char c : int_part) val = val * 10.0 + (c - '0');
    double frac = 0.0;
    double divisor = 10.0;
    for (char c : frac_part) {
      frac += (c - '0') / divisor;
      divisor *= 10.0;
    }
    val += frac;
    default_decay_time_real_ = val;
    default_decay_time_ = static_cast<uint64_t>(val);
    default_decay_time_infinite_ = false;
  } else {
    // Integer constant.
    for (char c : arg) {
      if (!std::isdigit(static_cast<unsigned char>(c))) {
        diag_.Error(loc, "invalid `default_decay_time argument: '" +
                             std::string(arg) + "'");
        return;
      }
    }
    uint64_t val = 0;
    for (char c : arg) val = val * 10 + (c - '0');
    default_decay_time_ = val;
    default_decay_time_real_ = static_cast<double>(val);
    default_decay_time_infinite_ = false;
  }
}

void Preprocessor::HandleDefaultTriregStrength(std::string_view rest,
                                               SourceLoc loc) {
  auto arg = TrimDirective(rest);
  if (arg.empty()) {
    diag_.Error(loc, "`default_trireg_strength requires an argument");
    return;
  }
  for (char c : arg) {
    if (!std::isdigit(static_cast<unsigned char>(c))) {
      diag_.Error(loc, "invalid `default_trireg_strength argument: '" +
                           std::string(arg) + "'");
      return;
    }
  }
  uint32_t val = 0;
  for (char c : arg) val = val * 10 + (c - '0');
  // §E.3: value must be between 0 and 250.
  if (val > 250) {
    diag_.Error(loc, "`default_trireg_strength value must be between 0 and 250");
    return;
  }
  default_trireg_strength_ = val;
  has_default_trireg_strength_ = true;
}

}  // namespace delta
