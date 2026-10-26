#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <optional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/keywords.h"
#include "preprocessor/preprocessor.h"

namespace delta {

static std::string_view TrimDirective(std::string_view s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front())))
    s.remove_prefix(1);
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back())))
    s.remove_suffix(1);
  return s;
}

enum class TimescaleParseStatus : std::uint8_t { kOk, kStep, kInvalid };

static TimescaleParseStatus ParseTimescaleComponentStatus(std::string_view text,
                                                          int& magnitude,
                                                          TimeUnit& unit) {
  auto trimmed = TrimDirective(text);
  if (trimmed.empty()) return TimescaleParseStatus::kInvalid;

  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) return TimescaleParseStatus::kInvalid;

  int mag = 0;
  for (size_t j = 0; j < i; ++j) {
    mag = mag * 10 + (trimmed[j] - '0');
  }
  if (mag != 1 && mag != 10 && mag != 100)
    return TimescaleParseStatus::kInvalid;
  magnitude = mag;

  auto unit_str = TrimDirective(trimmed.substr(i));
  if (unit_str == "step") return TimescaleParseStatus::kStep;
  return ParseTimeUnitStr(unit_str, unit) ? TimescaleParseStatus::kOk
                                          : TimescaleParseStatus::kInvalid;
}

void Preprocessor::HandleTimescale(std::string_view rest, SourceLoc loc) {
  auto slash = rest.find('/');
  if (slash == std::string_view::npos) {
    diag_.Error(loc, "invalid `timescale format: missing '/'",
                Subclause("22.7"));
    return;
  }
  auto unit_part = rest.substr(0, slash);
  auto prec_part = rest.substr(slash + 1);

  TimeScale ts;
  auto unit_status =
      ParseTimescaleComponentStatus(unit_part, ts.magnitude, ts.unit);
  if (unit_status == TimescaleParseStatus::kStep) {
    diag_.Error(
        loc, "step cannot be used to set or modify the time unit or precision",
        Subclause("3.14.3"));
    return;
  }
  if (unit_status != TimescaleParseStatus::kOk) {
    diag_.Error(loc, "invalid `timescale unit", Subclause("22.7"));
    return;
  }
  auto prec_status =
      ParseTimescaleComponentStatus(prec_part, ts.prec_magnitude, ts.precision);
  if (prec_status == TimescaleParseStatus::kStep) {
    diag_.Error(
        loc, "step cannot be used to set or modify the time unit or precision",
        Subclause("3.14.3"));
    return;
  }
  if (prec_status != TimescaleParseStatus::kOk) {
    diag_.Error(loc, "invalid `timescale precision", Subclause("22.7"));
    return;
  }

  if (EffectiveTimeOrder(ts.precision, ts.prec_magnitude) >
      EffectiveTimeOrder(ts.unit, ts.magnitude)) {
    diag_.Error(loc, "`timescale precision is less precise than the time unit",
                Subclause("22.7"));
    return;
  }

  current_timescale_ = ts;
  // §3.14.3: the finest precision is the one of the smallest order, its
  // magnitude counted, so a 10ps directive is finer than a 100ps one.
  if (!has_global_precision_ ||
      EffectiveTimeOrder(ts.precision, ts.prec_magnitude) <
          EffectiveTimeOrder(global_precision_, global_precision_magnitude_)) {
    global_precision_ = ts.precision;
    global_precision_magnitude_ = ts.prec_magnitude;
  }
  has_timescale_ = true;
  has_global_precision_ = true;
}

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
    diag_.Error(loc, "invalid net type '" + std::string(name) + "'",
                Subclause("22.8"));
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
        loc, "invalid `unconnected_drive argument: '" + std::string(arg) + "'",
        Subclause("22.9"));
  }
}

void Preprocessor::HandleLine(std::string_view rest, SourceLoc loc) {
  auto trimmed = TrimDirective(rest);
  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) {
    diag_.Error(loc, "invalid `line directive: missing or invalid line number",
                Subclause("22.12"));
    return;
  }
  uint32_t new_line = 0;
  for (size_t j = 0; j < i; ++j) {
    new_line = new_line * 10 + (trimmed[j] - '0');
  }

  if (new_line == 0) {
    diag_.Error(loc, "`line number must be a positive integer",
                Subclause("22.12"));
    return;
  }

  auto after_num = TrimDirective(trimmed.substr(i));
  if (after_num.empty() || after_num[0] != '"') {
    diag_.Error(loc, "`line directive requires a quoted filename",
                Subclause("22.12"));
    return;
  }
  auto end_quote = after_num.find('"', 1);
  if (end_quote == std::string_view::npos) {
    diag_.Error(loc, "unterminated string in `line directive",
                Subclause("22.12"));
    return;
  }
  auto filename = after_num.substr(1, end_quote - 1);

  auto after_file = TrimDirective(after_num.substr(end_quote + 1));
  if (after_file.empty() ||
      !std::isdigit(static_cast<unsigned char>(after_file[0]))) {
    diag_.Error(loc, "`line directive requires a level (0, 1, or 2)",
                Subclause("22.12"));
    return;
  }
  int level = after_file[0] - '0';
  if (level > 2) {
    diag_.Error(loc, "`line level must be 0, 1, or 2", Subclause("22.12"));
    return;
  }

  auto after_level = TrimDirective(after_file.substr(1));
  if (!after_level.empty()) {
    diag_.Error(loc, "only whitespace may appear on the same line as `line",
                Subclause("22.12"));
    return;
  }

  line_offset_ = new_line;
  line_override_src_line_ = loc.line;
  has_line_override_ = true;
  line_file_override_ = std::string(filename);
  TakeLineFileOverrideId();
}

// §22.12 has a `line directive set the file name of the line that follows it,
// so the name it gave is registered and its id kept for the origins of those
// lines. The file is registered with no content, because this run was handed
// the file the directive appears in and never the one it names: a report can
// say where the line came from, and SourceManager::GetLineText finds nothing
// to quote back, which is correct.
//
// One id is kept per name rather than one per directive, because a
// machine-generated source carries a `line on many of its lines and
// registering each would leave SourceManager holding one entry per directive.
//
// The empty name `""` is a name too, a string literal §22.12 makes the file's
// name like any other, so it is registered as one.
void Preprocessor::TakeLineFileOverrideId() {
  auto it = line_file_override_ids_.find(line_file_override_);
  if (it == line_file_override_ids_.end()) {
    it = line_file_override_ids_
             .emplace(line_file_override_,
                      src_mgr_.AddFile(line_file_override_, ""))
             .first;
  }
  line_file_override_id_ = it->second;
}

// §22.4 (printed page 705): a relative filename written in double quotes is
// looked for in the compiler's current working directory and then in any
// locations the user names, while an absolute filename is taken as it stands
// and nowhere else. The including file's own directory, `src_dir`, and the -I
// directories are this tool's user-specified locations, searched after the
// working directory; a name in angle brackets is looked for in those alone.
// Looked for beside the including file alone, a quoted name went unfound
// whenever that file was named on the command line without a directory, since
// its directory then read as empty.
std::string Preprocessor::ResolveInclude(std::string_view filename,
                                         const std::string& src_dir,
                                         bool quoted) {
  // HandleInclude, the one caller, has already refused an empty name.
  if (filename[0] == '/') {
    std::string path{filename};
    std::ifstream ifs(path);
    if (ifs.good()) return path;
    return "";
  }

  if (quoted) {
    std::string path{filename};
    std::ifstream ifs(path);
    if (ifs.good()) return path;
  }
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
    diag_.Error(loc, "expected quoted version string after `begin_keywords",
                Subclause("22.14"));
    return;
  }
  auto spec = rest.substr(start + 1, end - start - 1);
  auto version = ParseKeywordVersion(spec);
  if (!version) {
    diag_.Error(loc,
                "unrecognized version specifier: \"" + std::string(spec) + "\"",
                Subclause("22.14"));
    return;
  }
  keyword_version_stack_.push_back({*version, loc});
  // The marker and the version byte are the whole of this line's output.
  // RunPreprocLoop in src/preprocessor/preprocessor.cpp ends the directive's
  // line as it ends every other line, so a newline written here would be a
  // second one and would put every line below the directive one line further
  // down than the user wrote it.
  output += kKeywordMarker;
  output += static_cast<char>(static_cast<uint8_t>(*version));
}

void Preprocessor::HandleEndKeywords(SourceLoc loc, std::string& output) {
  if (keyword_version_stack_.empty()) {
    diag_.Error(loc, "`end_keywords without matching `begin_keywords",
                Subclause("22.14"));
    return;
  }
  keyword_version_stack_.pop_back();
  // Nested pairs are stacked, so closing one returns to the version_specifier
  // that was in effect just outside it; with nothing left the reserved word
  // list falls back to this implementation's default set.
  auto version = keyword_version_stack_.empty()
                     ? KeywordVersion::kVer18002023
                     : keyword_version_stack_.back().version;
  // Ended by RunPreprocLoop rather than here, for the reason given in
  // HandleBeginKeywords.
  output += kKeywordMarker;
  output += static_cast<char>(static_cast<uint8_t>(version));
}

// §22.14 requires the two directives to be used as a pair, `begin_keywords
// first and `end_keywords sometime later. Any region still open once the last
// source file has been consumed never received its closing directive.
void Preprocessor::ReportUnterminatedKeywordRegions() {
  for (const auto& region : keyword_version_stack_) {
    diag_.Error(region.loc, "`begin_keywords without matching `end_keywords",
                Subclause("22.14"));
  }
  keyword_version_stack_.clear();
}

void Preprocessor::BeginCompilationUnit() {
  ReportUnterminatedKeywordRegions();
  macros_ = initial_macros_;
  ResetDirectiveState();
  ResetAllPragmas();
  // §5.6.4: a `line read in the unit before shall not number this one's lines.
  has_line_override_ = false;
}

// The value the digit `c` stands for in base `radix`, or -1 where it is none
// of that base's digits, as §5.7.1's x, z and ? digits are none.
static int DigitValue(char c, unsigned radix) {
  static constexpr std::string_view kDigits = "0123456789abcdef";
  size_t value = kDigits.find(
      static_cast<char>(std::tolower(static_cast<unsigned char>(c))));
  return value < radix ? static_cast<int>(value) : -1;
}

// §5.7.1's digits of base `radix`, with an underscore anywhere but first, as
// the value they spell, or nothing where `text` is not such a run.
static std::optional<uint64_t> ReadDigits(std::string_view text,
                                          unsigned radix) {
  if (text.empty() || DigitValue(text.front(), radix) < 0) return std::nullopt;
  uint64_t value = 0;
  for (char c : text) {
    if (c == '_') continue;
    int digit = DigitValue(c, radix);
    if (digit < 0) return std::nullopt;
    value = value * radix + static_cast<uint64_t>(digit);
  }
  return value;
}

// The radix §5.7.1's base format letter `c` names, or 0 for a letter naming
// none.
static unsigned RadixOf(char c) {
  static constexpr std::string_view kLetters = "bodh";
  static constexpr unsigned kRadixes[] = {2, 8, 10, 16};
  size_t at = kLetters.find(
      static_cast<char>(std::tolower(static_cast<unsigned char>(c))));
  return at == std::string_view::npos ? 0 : kRadixes[at];
}

// §5.7.1's based number, `size_text` the size written before its apostrophe,
// empty where none was, and `format` the text after it: an optional s, the base
// letter and the digits, white space allowed before the digits. The value is
// held in the constant's width, its size where it has one and 64 bits where
// not, so a narrower size truncates the digits from the left and a signed
// constant whose top bit is set is negative.
static std::optional<int64_t> ReadBasedConstant(std::string_view size_text,
                                                std::string_view format) {
  bool is_signed = format.find_first_of("sS") == 0;
  format.remove_prefix(is_signed ? 1 : 0);
  unsigned radix = format.empty() ? 0 : RadixOf(format.front());
  if (radix == 0) return std::nullopt;
  auto digits = ReadDigits(TrimDirective(format.substr(1)), radix);
  uint64_t width = 64;
  if (!size_text.empty()) {
    auto size = ReadDigits(size_text, 10);
    if (!size || *size == 0) return std::nullopt;
    width = std::min<uint64_t>(*size, 64);
  }
  if (!digits) return std::nullopt;
  uint64_t mask = width == 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  uint64_t value = *digits & mask;
  bool negative = is_signed && (value >> (width - 1)) != 0;
  return static_cast<int64_t>(negative ? value | ~mask : value);
}

// An integer constant as §5.7.1 writes one, an unsized decimal number or a
// based number, as the value it stands for, or nothing where `arg` is none.
static std::optional<int64_t> ReadIntegerConstant(std::string_view arg) {
  size_t quote = arg.find('\'');
  if (quote != std::string_view::npos) {
    return ReadBasedConstant(TrimDirective(arg.substr(0, quote)),
                             arg.substr(quote + 1));
  }
  auto value = ReadDigits(arg, 10);
  if (!value) return std::nullopt;
  return static_cast<int64_t>(*value);
}

// The length of §5.7.1's unsigned number at the start of `text`, decimal digits
// with underscores after the first, or 0 where none starts there.
static size_t UnsignedNumberLength(std::string_view text) {
  if (text.empty() || !std::isdigit(static_cast<unsigned char>(text.front()))) {
    return 0;
  }
  size_t length = 1;
  while (length < text.size() &&
         (std::isdigit(static_cast<unsigned char>(text[length])) ||
          text[length] == '_')) {
    ++length;
  }
  return length;
}

// A real constant as §5.7.2 writes one, in decimal notation with a digit on
// each side of the point or in scientific notation with an optionally signed
// exponent, underscores ignored, as the value it stands for, or nothing where
// `arg` is none. A run of digits alone reads as a real too.
static std::optional<double> ReadRealConstant(std::string_view arg) {
  size_t end = UnsignedNumberLength(arg);
  if (end == 0) return std::nullopt;
  if (arg.substr(end).starts_with('.')) {
    size_t digits = UnsignedNumberLength(arg.substr(end + 1));
    if (digits == 0) return std::nullopt;
    end += 1 + digits;
  }
  std::string_view rest = arg.substr(end);
  if (rest.find_first_of("eE") == 0) {
    size_t sign = rest.find_first_of("+-", 1) == 1 ? 1 : 0;
    size_t digits = UnsignedNumberLength(rest.substr(1 + sign));
    if (digits == 0) return std::nullopt;
    end += 1 + sign + digits;
  }
  if (end != arg.size()) return std::nullopt;
  std::string text;
  for (char c : arg) {
    if (c != '_') text.push_back(c);
  }
  return std::strtod(text.c_str(), nullptr);
}

void Preprocessor::HandleDefaultDecayTime(std::string_view rest,
                                          SourceLoc loc) {
  auto arg = TrimDirective(rest);
  if (arg.empty()) {
    diag_.Error(loc, "`default_decay_time requires an argument",
                Subclause("E.2"));
    return;
  }
  if (arg == "infinite") {
    default_decay_time_infinite_ = true;
    default_decay_time_ = 0;
    default_decay_time_real_ = 0.0;
    return;
  }
  // E.2 takes an integer constant or a real constant. A charge decay time has
  // no negative value (§28.16.2), so a signed integer constant whose value is
  // negative is no decay time.
  std::optional<double> value;
  if (auto integer = ReadIntegerConstant(arg)) {
    if (*integer >= 0) value = static_cast<double>(*integer);
  } else {
    value = ReadRealConstant(arg);
  }
  if (!value) {
    diag_.Error(
        loc, "invalid `default_decay_time argument: '" + std::string(arg) + "'",
        Subclause("E.2"));
    return;
  }
  // §3.14.1: the time precision governs how a delay value is rounded before
  // simulation uses it, and a precision equal to the time unit rounds each
  // delay value to an integer.
  // E.2 admits a real_constant here and gives no conversion of its own, so
  // the rounding is that clause's, not a truncation: 3.5 is a decay time of
  // 4. The exact value stays in default_decay_time_real_.
  default_decay_time_real_ = *value;
  default_decay_time_ = static_cast<uint64_t>(std::llround(*value));
  default_decay_time_infinite_ = false;
}

void Preprocessor::HandleDefaultTriregStrength(std::string_view rest,
                                               SourceLoc loc) {
  auto arg = TrimDirective(rest);
  if (arg.empty()) {
    diag_.Error(loc, "`default_trireg_strength requires an argument",
                Subclause("E.3"));
    return;
  }
  auto value = ReadIntegerConstant(arg);
  if (!value) {
    diag_.Error(
        loc,
        "invalid `default_trireg_strength argument: '" + std::string(arg) + "'",
        Subclause("E.3"));
    return;
  }
  if (*value < 0 || *value > 250) {
    diag_.Error(loc, "`default_trireg_strength value must be between 0 and 250",
                Subclause("E.3"));
    return;
  }
  default_trireg_strength_ = static_cast<uint32_t>(*value);
  has_default_trireg_strength_ = true;
}

}  // namespace delta
