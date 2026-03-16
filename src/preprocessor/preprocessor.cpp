#include "preprocessor/preprocessor.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>

namespace delta {

Preprocessor::Preprocessor(SourceManager& src_mgr, DiagEngine& diag,
                           PreprocConfig config)
    : src_mgr_(src_mgr), diag_(diag), config_(std::move(config)) {
  for (const auto& [name, value] : config_.defines) {
    MacroDef def;
    def.name = name;
    def.body = value;
    macros_.Define(std::move(def));
  }
  // IEEE 1800-2023 Table 22-2: predefined coverage macros.
  DefinePredefined("SV_COV_START", "0");
  DefinePredefined("SV_COV_STOP", "1");
  DefinePredefined("SV_COV_RESET", "2");
  DefinePredefined("SV_COV_CHECK", "3");
  DefinePredefined("SV_COV_MODULE", "10");
  DefinePredefined("SV_COV_HIER", "11");
  DefinePredefined("SV_COV_ASSERTION", "20");
  DefinePredefined("SV_COV_FSM_STATE", "21");
  DefinePredefined("SV_COV_STATEMENT", "22");
  DefinePredefined("SV_COV_TOGGLE", "23");
  DefinePredefined("SV_COV_OVERFLOW", "-2");
  DefinePredefined("SV_COV_ERROR", "-1");
  DefinePredefined("SV_COV_NOCOV", "0");
  DefinePredefined("SV_COV_OK", "1");
  DefinePredefined("SV_COV_PARTIAL", "2");
}

void Preprocessor::DefinePredefined(std::string name, std::string body) {
  MacroDef def;
  def.name = std::move(name);
  def.body = std::move(body);
  macros_.Define(std::move(def));
}

std::string Preprocessor::Preprocess(uint32_t file_id) {
  auto content = src_mgr_.FileContent(file_id);
  return ProcessSource(content, file_id, 0);
}

std::string_view Preprocessor::Trim(std::string_view s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
    s.remove_prefix(1);
  }
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
    s.remove_suffix(1);
  }
  return s;
}

// §22.5.1: Compiler directive names that cannot be redefined as macros.
bool IsCompilerDirective(std::string_view name) {
  static constexpr std::string_view kDirectives[] = {
      "define",
      "undef",
      "undefineall",
      "ifdef",
      "ifndef",
      "elsif",
      "else",
      "endif",
      "include",
      "timescale",
      "resetall",
      "line",
      "pragma",
      "celldefine",
      "endcelldefine",
      "default_nettype",
      "unconnected_drive",
      "nounconnected_drive",
      "begin_keywords",
      "end_keywords",
      "default_decay_time",
      "default_trireg_strength",
      "delay_mode_distributed",
      "delay_mode_path",
      "delay_mode_unit",
      "delay_mode_zero",
  };
  for (auto d : kDirectives) {
    if (name == d) return true;
  }
  return false;
}

// Returns true if the character at position i is a backtick-quote (`") or
// backtick-escaped-quote (`\`") delimiter, advancing i past the sequence.
static bool SkipBacktickQuote(std::string_view body, size_t& i) {
  if (body[i] != '`') return false;
  if (i + 1 < body.size() && body[i + 1] == '"') {
    i += 1;
    return true;
  }
  if (i + 3 < body.size() && body[i + 1] == '\\' && body[i + 2] == '`' &&
      body[i + 3] == '"') {
    i += 3;
    return true;
  }
  return false;
}

// Process an unescaped quote character, updating triple-quote and
// single-string tracking state. Advances i past triple-quote sequences.
static void ProcessQuoteChar(std::string_view body, size_t& i, bool& in_string,
                             bool& in_triple) {
  if (in_triple) {
    if (i + 2 < body.size() && body[i + 1] == '"' && body[i + 2] == '"') {
      in_triple = false;
      i += 2;
    }
    return;
  }
  if (in_string) {
    in_string = false;
    return;
  }
  if (i + 2 < body.size() && body[i + 1] == '"' && body[i + 2] == '"') {
    in_triple = true;
    i += 2;
    return;
  }
  in_string = true;
}

// §22.5.1: Check for unterminated string literals in macro bodies.
// Handles triple-quoted strings (""") and `" (backtick-quote) delimiters.
bool HasUnterminatedString(std::string_view body) {
  bool in_string = false;
  bool in_triple = false;
  for (size_t i = 0; i < body.size(); ++i) {
    if (SkipBacktickQuote(body, i)) continue;
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
      ProcessQuoteChar(body, i, in_string, in_triple);
    }
  }
  return in_string || in_triple;
}

static bool EndsWithBackslash(std::string_view line) {
  return !line.empty() && line.back() == '\\';
}

// Count unmatched triple-quote sequences in text, skipping backtick-prefixed
// `""" sequences which are a distinct operator (§22.5.1).
static bool HasOpenTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 2 < text.size(); ++i) {
    if (text[i] == '"' && text[i + 1] == '"' && text[i + 2] == '"') {
      if (i > 0 && text[i - 1] == '`') {
        i += 2;
        continue;
      }
      ++count;
      i += 2;
    }
  }
  return count % 2 != 0;
}

// §22.5.1: Count unmatched backtick-triple-quote (`""") sequences.
static bool HasOpenBacktickTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 3 < text.size(); ++i) {
    if (text[i] == '`' && text[i + 1] == '"' && text[i + 2] == '"' &&
        text[i + 3] == '"') {
      ++count;
      i += 3;
    }
  }
  return count % 2 != 0;
}

// Returns true if character at i is an unescaped quote (not preceded by
// backslash or backtick), toggling string state when outside a block comment.
static bool IsUnescapedQuote(std::string_view text, size_t i) {
  return text[i] == '"' && (i == 0 || text[i - 1] != '\\') &&
         (i == 0 || text[i - 1] != '`');
}

// Advance past a block-comment delimiter if present. Returns true if a
// comment-open or comment-close was consumed, updating in_block accordingly.
static bool TryToggleBlockComment(std::string_view text, size_t& i,
                                  bool& in_block) {
  if (i + 1 >= text.size()) return false;
  if (!in_block && text[i] == '/' && text[i + 1] == '*') {
    in_block = true;
    ++i;
    return true;
  }
  if (in_block && text[i] == '*' && text[i + 1] == '/') {
    in_block = false;
    ++i;
    return true;
  }
  return false;
}

// Check for an unclosed block comment in text.
static bool HasOpenBlockComment(std::string_view text) {
  bool in_string = false;
  bool in_block = false;
  for (size_t i = 0; i < text.size(); ++i) {
    if (IsUnescapedQuote(text, i)) {
      if (!in_block) in_string = !in_string;
      continue;
    }
    if (in_string) continue;
    TryToggleBlockComment(text, i, in_block);
  }
  return in_block;
}

// §22.5.1: Join a `define body that spans multiple lines via backslash,
// triple-quoted strings, or block comments.
static std::string JoinDefineBody(std::string_view src, size_t pos, size_t& eol,
                                  uint32_t& line_num) {
  std::string_view first_line = src.substr(pos, eol - pos);
  std::string joined;

  // Start with the first line, stripping trailing backslash if present.
  if (EndsWithBackslash(first_line)) {
    joined.assign(first_line.substr(0, first_line.size() - 1));
  } else {
    joined.assign(first_line);
  }

  // Keep joining while the current text has: trailing backslash (already
  // stripped), open triple-quote, or open block comment.
  auto needs_continuation = [](std::string_view line_text,
                               const std::string& accumulated) {
    if (EndsWithBackslash(line_text)) return true;
    if (HasOpenTripleQuote(accumulated)) return true;
    if (HasOpenBlockComment(accumulated)) return true;
    return false;
  };

  while (eol < src.size() && needs_continuation(first_line, joined)) {
    size_t next_start = eol + 1;
    size_t next_eol = src.find('\n', next_start);
    if (next_eol == std::string_view::npos) next_eol = src.size();
    std::string_view next_line = src.substr(next_start, next_eol - next_start);
    ++line_num;
    eol = next_eol;
    first_line = next_line;  // For next backslash check.
    // §22.5.1: Inside `""", backslash-newline preserves the newline
    // (only the backslash is removed).
    if (HasOpenBacktickTripleQuote(joined)) {
      joined += '\n';
    }
    if (EndsWithBackslash(next_line)) {
      joined.append(next_line.substr(0, next_line.size() - 1));
    } else {
      joined.append(next_line);
    }
  }
  return joined;
}

static bool StartsWithDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  if (trimmed.size() < dir.size() + 1) {
    return false;
  }
  if (trimmed[0] != '`') {
    return false;
  }
  return trimmed.substr(1, dir.size()) == dir;
}

static std::string_view AfterDirective(std::string_view line,
                                       std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  auto rest = trimmed.substr(1 + dir.size());
  return Preprocessor::Trim(rest);
}

// §22.2: Split a single-token directive argument from the remainder text.
static std::pair<std::string_view, std::string_view> SplitFirstToken(
    std::string_view s) {
  size_t end = 0;
  while (end < s.size() && !std::isspace(static_cast<unsigned char>(s[end])))
    ++end;
  if (end >= s.size()) return {s, {}};
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

// §22.2: Split `timescale argument (unit / precision) from remainder.
// Expects expanded text (macros already substituted).
static std::pair<std::string_view, std::string_view> SplitTimescaleArg(
    std::string_view s) {
  auto slash = s.find('/');
  if (slash == std::string_view::npos) return {s, {}};
  auto after_slash = s.substr(slash + 1);
  auto prec = Preprocessor::Trim(after_slash);
  size_t end = 0;
  // Skip digits (magnitude: 1, 10, 100).
  while (end < prec.size() &&
         std::isdigit(static_cast<unsigned char>(prec[end])))
    ++end;
  // Skip whitespace between magnitude and unit.
  while (end < prec.size() &&
         std::isspace(static_cast<unsigned char>(prec[end])))
    ++end;
  // Skip alpha chars (unit: s, ms, us, ns, ps, fs).
  while (end < prec.size() &&
         std::isalpha(static_cast<unsigned char>(prec[end])))
    ++end;
  auto ts_end = static_cast<size_t>(prec.data() + end - s.data());
  return {s.substr(0, ts_end), Preprocessor::Trim(s.substr(ts_end))};
}

// §22.2: Split `begin_keywords quoted argument from remainder.
static std::pair<std::string_view, std::string_view> SplitQuotedArg(
    std::string_view s) {
  auto first = s.find('"');
  if (first == std::string_view::npos) return {s, {}};
  auto second = s.find('"', first + 1);
  if (second == std::string_view::npos) return {s, {}};
  auto end = second + 1;
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

// Consume characters inside a block comment, replacing content with spaces
// until the closing */ is found. Returns true if the block comment was closed.
static bool StripBlockCommentContent(std::string_view line, size_t& i,
                                     std::string& result) {
  if (i + 1 < line.size() && line[i] == '*' && line[i + 1] == '/') {
    result += "*/";
    i += 2;
    return true;
  }
  result += ' ';
  ++i;
  return false;
}

// Process a single character outside of strings and comments, detecting
// line comments (//) and block comment starts (/*). Returns true if a
// line comment was found (caller should stop processing).
static bool StripNormalChar(std::string_view line, size_t& i,
                            std::string& result, bool& in_block_comment) {
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '/') {
    result += "//";
    i += 2;
    while (i < line.size()) {
      result += ' ';
      ++i;
    }
    return true;
  }
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '*') {
    result += "/*";
    i += 2;
    in_block_comment = true;
    return false;
  }
  result += line[i++];
  return false;
}

// §22.2: Replace comment content with spaces so backticks within comments
// are not processed by ExpandInlineMacros. Tracks block comment state.
static std::string StripComments(std::string_view line,
                                 bool& in_block_comment) {
  std::string result;
  result.reserve(line.size());
  bool in_string = false;
  size_t i = 0;

  while (i < line.size()) {
    if (in_block_comment) {
      if (StripBlockCommentContent(line, i, result)) in_block_comment = false;
      continue;
    }
    if (line[i] == '"' && (i == 0 || line[i - 1] != '\\')) {
      in_string = !in_string;
      result += line[i++];
      continue;
    }
    if (in_string) {
      result += line[i++];
      continue;
    }
    if (StripNormalChar(line, i, result, in_block_comment)) return result;
  }
  return result;
}

// Expand macros, conditionals, and strip comments for a non-directive line,
// appending the result to output.
void Preprocessor::ExpandAndAppendLine(std::string_view line, uint32_t file_id,
                                       uint32_t line_num, std::string& output) {
  auto stripped = StripComments(line, in_block_comment_);
  auto conditioned = ExpandInlineConditionals(stripped);
  auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  output.append(expanded);
}

// §22.2: After stripping comments, find the start of a directive that was
// hidden behind comments or whitespace.  Returns the position in `stripped`
// where the backtick begins, or npos if the first meaningful character is
// not a backtick.
static size_t FindDirectiveInStripped(std::string_view stripped) {
  size_t i = 0;
  while (i < stripped.size()) {
    auto c = stripped[i];
    if (std::isspace(static_cast<unsigned char>(c))) {
      ++i;
      continue;
    }
    // Skip preserved comment shells left by StripComments.
    if (i + 1 < stripped.size() && c == '/' && stripped[i + 1] == '*') {
      auto close = stripped.find("*/", i + 2);
      if (close != std::string_view::npos) {
        i = close + 2;
        continue;
      }
      break;
    }
    if (i + 1 < stripped.size() && c == '/' && stripped[i + 1] == '/') {
      break;
    }
    return (c == '`') ? i : std::string_view::npos;
  }
  return std::string_view::npos;
}

// Handle a line that falls inside an open block comment. Passes through
// comment text and processes any remainder after the closing */.
// Returns true if the line was consumed (caller should advance to next line).
bool Preprocessor::ProcessBlockCommentLine(std::string_view line,
                                           uint32_t file_id, uint32_t line_num,
                                           int depth, std::string& output) {
  auto close = line.find("*/");
  if (close == std::string_view::npos) {
    output.append(line);
    output.push_back('\n');
    return true;
  }
  output.append(line.substr(0, close + 2));
  in_block_comment_ = false;
  auto remainder = line.substr(close + 2);
  if (!Trim(remainder).empty()) {
    bool handled =
        ProcessDirective(remainder, file_id, line_num, depth, output);
    if (!handled && IsActive()) {
      ExpandAndAppendLine(remainder, file_id, line_num, output);
    }
  }
  output.push_back('\n');
  return true;
}

std::string Preprocessor::ProcessSource(std::string_view src, uint32_t file_id,
                                        int depth) {
  if (depth > kMaxIncludeDepth) {
    diag_.Error({file_id, 1, 1}, "include depth exceeds maximum of 15");
    return "";
  }

  std::string output;
  output.reserve(src.size());
  uint32_t line_num = 0;
  size_t pos = 0;

  while (pos < src.size()) {
    size_t eol = src.find('\n', pos);
    if (eol == std::string_view::npos) eol = src.size();
    std::string_view line = src.substr(pos, eol - pos);
    ++line_num;

    if (in_block_comment_) {
      ProcessBlockCommentLine(line, file_id, line_num, depth, output);
      pos = eol + 1;
      continue;
    }

    // §22.5.1: Join multi-line `define (backslash, triple-quote, block
    // comment).
    std::string joined;
    if (StartsWithDirective(line, "define")) {
      auto body_start = AfterDirective(line, "define");
      if (EndsWithBackslash(line) || HasOpenTripleQuote(body_start) ||
          HasOpenBlockComment(body_start)) {
        joined = JoinDefineBody(src, pos, eol, line_num);
        line = joined;
      }
    }

    bool handled = ProcessDirective(line, file_id, line_num, depth, output);
    if (!handled && IsActive()) {
      // §22.2: A language element is allowed before a directive on the same
      // line.  Strip comments and check whether the remaining text begins
      // with a directive (e.g. after an inline block comment).
      auto stripped = StripComments(std::string(line), in_block_comment_);
      size_t dir_pos = FindDirectiveInStripped(stripped);
      if (dir_pos != std::string_view::npos) {
        if (dir_pos > 0) output.append(stripped, 0, dir_pos);
        auto dir_text = std::string_view(stripped).substr(dir_pos);
        if (!ProcessDirective(dir_text, file_id, line_num, depth, output)) {
          auto conditioned = ExpandInlineConditionals(std::string(dir_text));
          auto expanded =
              ExpandInlineMacros(conditioned, file_id, line_num);
          TrackDesignElement(Trim(expanded));
          output.append(expanded);
        }
      } else {
        auto conditioned = ExpandInlineConditionals(stripped);
        auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
        TrackDesignElement(Trim(expanded));
        output.append(expanded);
      }
    }
    output.push_back('\n');
    pos = eol + 1;
  }
  return output;
}

// §22.2: Process arbitrary text — strip comments, expand macros, track design
// elements, and append to output.
void Preprocessor::OutputText(std::string_view text, uint32_t file_id,
                              uint32_t line_num, std::string& output) {
  if (Trim(text).empty()) return;
  auto stripped = StripComments(text, in_block_comment_);
  auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  output.append(expanded);
}

// §22.2: Process pre-expanded text — strip comments and track design elements,
// but skip macro expansion (already done by caller).
void Preprocessor::OutputPreExpanded(std::string_view text,
                                     std::string& output) {
  if (Trim(text).empty()) return;
  auto stripped = StripComments(text, in_block_comment_);
  TrackDesignElement(Trim(std::string_view(stripped)));
  output.append(stripped);
}

// §22.2: Output text that follows a directive with a defined end on the
// same line.  Applies macro expansion and comment stripping.
void Preprocessor::OutputRemainder(std::string_view line,
                                   std::string_view directive, uint32_t file_id,
                                   uint32_t line_num, std::string& output) {
  OutputText(AfterDirective(line, directive), file_id, line_num, output);
}

// Returns true (and emits an error) if currently inside a design element,
// which makes the given directive illegal.
bool Preprocessor::RejectInsideDesignElement(std::string_view directive_name,
                                             SourceLoc loc) {
  if (design_element_depth_ == 0) return false;
  std::string msg = "`";
  msg.append(directive_name);
  msg.append(" illegal inside a design element");
  diag_.Error(loc, msg);
  return true;
}

// §22.3: Reset all resettable directive state.
void Preprocessor::ResetDirectiveState() {
  default_net_type_ = NetType::kWire;
  in_celldefine_ = false;
  unconnected_drive_ = NetType::kWire;
  has_timescale_ = false;
  current_timescale_ = TimeScale{};
  default_decay_time_ = 0;
  default_decay_time_real_ = 0.0;
  default_decay_time_infinite_ = true;
  default_trireg_strength_ = 0;
  has_default_trireg_strength_ = false;
  delay_mode_directive_ = DelayModeDirective::kNone;
}

// Annex E: Handle delay_mode_* directives.
bool Preprocessor::ProcessDelayModeDirective(std::string_view line,
                                             SourceLoc loc) {
  if (StartsWithDirective(line, "delay_mode_distributed")) {
    if (RejectInsideDesignElement("delay_mode_distributed", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kDistributed;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_path")) {
    if (RejectInsideDesignElement("delay_mode_path", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kPath;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_unit")) {
    if (RejectInsideDesignElement("delay_mode_unit", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kUnit;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_zero")) {
    if (RejectInsideDesignElement("delay_mode_zero", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kZero;
    return true;
  }
  return false;
}

bool Preprocessor::ProcessSimpleStateDirective(std::string_view line,
                                               SourceLoc loc, uint32_t file_id,
                                               uint32_t line_num,
                                               std::string& output) {
  if (StartsWithDirective(line, "endcelldefine")) {
    in_celldefine_ = false;
    OutputRemainder(line, "endcelldefine", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "celldefine")) {
    in_celldefine_ = true;
    OutputRemainder(line, "celldefine", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "pragma")) {
    auto rest = Trim(AfterDirective(line, "pragma"));
    if (rest.empty()) {
      diag_.Error(loc, "`pragma requires a pragma_name");
    } else {
      char first = rest.front();
      if (!std::isalpha(static_cast<unsigned char>(first)) && first != '_') {
        diag_.Error(loc, "`pragma pragma_name must be a simple identifier");
      }
    }
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessExpandedStateDirective(std::string_view line,
                                                 SourceLoc loc,
                                                 uint32_t file_id,
                                                 uint32_t line_num,
                                                 std::string& output) {
  if (StartsWithDirective(line, "timescale")) {
    if (RejectInsideDesignElement("timescale", loc)) return true;
    auto rest = AfterDirective(line, "timescale");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [ts_arg, remainder] = SplitTimescaleArg(expanded);
    HandleTimescale(ts_arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "default_nettype")) {
    if (RejectInsideDesignElement("default_nettype", loc)) return true;
    auto rest = AfterDirective(line, "default_nettype");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleDefaultNettype(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "unconnected_drive")) {
    if (RejectInsideDesignElement("unconnected_drive", loc)) return true;
    auto rest = AfterDirective(line, "unconnected_drive");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleUnconnectedDrive(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "nounconnected_drive")) {
    if (RejectInsideDesignElement("nounconnected_drive", loc)) return true;
    unconnected_drive_ = NetType::kWire;
    OutputRemainder(line, "nounconnected_drive", file_id, line_num, output);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc,
                                         uint32_t file_id, uint32_t line_num,
                                         std::string& output) {
  if (ProcessSimpleStateDirective(line, loc, file_id, line_num, output))
    return true;
  if (ProcessExpandedStateDirective(line, loc, file_id, line_num, output))
    return true;
  if (StartsWithDirective(line, "resetall")) {
    if (RejectInsideDesignElement("resetall", loc)) return true;
    ResetDirectiveState();
    OutputRemainder(line, "resetall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "default_decay_time")) {
    if (RejectInsideDesignElement("default_decay_time", loc)) return true;
    HandleDefaultDecayTime(AfterDirective(line, "default_decay_time"), loc);
    return true;
  }
  if (StartsWithDirective(line, "default_trireg_strength")) {
    if (RejectInsideDesignElement("default_trireg_strength", loc)) return true;
    HandleDefaultTriregStrength(AfterDirective(line, "default_trireg_strength"),
                                loc);
    return true;
  }
  if (ProcessDelayModeDirective(line, loc)) return true;
  return false;
}

// Extract the macro name from a `undef argument, handling escaped identifiers.
static size_t FindUndefNameEnd(std::string_view text) {
  size_t name_end = 0;
  if (!text.empty() && text[0] == '\\') {
    name_end = 1;
    while (name_end < text.size() &&
           !std::isspace(static_cast<unsigned char>(text[name_end])))
      ++name_end;
  } else {
    while (name_end < text.size() && IsIdentChar(text[name_end])) ++name_end;
  }
  return name_end;
}

// Handle the `include directive: expand macros in the argument and delegate.
void Preprocessor::ProcessIncludeDirective(std::string_view line, SourceLoc loc,
                                           int depth, std::string& output) {
  auto inc_arg = AfterDirective(line, "include");
  auto expanded_arg = ExpandInlineMacros(inc_arg, loc.file_id, loc.line);
  auto trimmed_arg = Trim(std::string_view(expanded_arg));
  bool angle_bracket = !trimmed_arg.empty() && trimmed_arg.front() == '<';
  HandleInclude(expanded_arg, loc, depth, output, angle_bracket);
}

// Handle `begin_keywords / `end_keywords directives.
bool Preprocessor::ProcessKeywordsDirective(std::string_view line,
                                            SourceLoc loc, uint32_t file_id,
                                            uint32_t line_num,
                                            std::string& output) {
  if (StartsWithDirective(line, "begin_keywords")) {
    if (RejectInsideDesignElement("begin_keywords", loc)) return true;
    auto rest = AfterDirective(line, "begin_keywords");
    auto [bk_arg, remainder] = SplitQuotedArg(rest);
    HandleBeginKeywords(bk_arg, loc, output);
    OutputText(remainder, file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "end_keywords")) {
    if (RejectInsideDesignElement("end_keywords", loc)) return true;
    HandleEndKeywords(loc, output);
    OutputRemainder(line, "end_keywords", file_id, line_num, output);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessActiveOnlyDirective(std::string_view line,
                                              SourceLoc loc, int depth,
                                              std::string& output) {
  uint32_t file_id = loc.file_id;
  uint32_t line_num = loc.line;
  if (StartsWithDirective(line, "include")) {
    ProcessIncludeDirective(line, loc, depth, output);
    return true;
  }
  if (ProcessKeywordsDirective(line, loc, file_id, line_num, output))
    return true;
  if (ProcessStateDirective(line, loc, file_id, line_num, output)) return true;
  auto trimmed = Trim(line);
  return TryExpandMacro(trimmed, output, file_id, line_num, depth);
}

bool Preprocessor::ProcessDirective(std::string_view line, uint32_t file_id,
                                    uint32_t line_num, int depth,
                                    std::string& output) {
  auto trimmed = Trim(line);
  if (trimmed.empty() || trimmed[0] != '`') return false;
  SourceLoc loc = {file_id, line_num, 1};

  if (StartsWithDirective(line, "define")) {
    HandleDefine(AfterDirective(line, "define"), loc);
    return true;
  }
  if (StartsWithDirective(line, "undefineall")) {
    macros_.UndefineAll();
    OutputRemainder(line, "undefineall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "undef")) {
    auto trimmed_rest = Trim(AfterDirective(line, "undef"));
    size_t name_end = FindUndefNameEnd(trimmed_rest);
    HandleUndef(trimmed_rest.substr(0, name_end), loc);
    if (IsActive()) {
      OutputText(Trim(trimmed_rest.substr(name_end)), file_id, line_num,
                 output);
    }
    return true;
  }
  if (ProcessConditionalDirective(line, file_id, line_num, output)) return true;
  if (IsActive() && ProcessActiveOnlyDirective(line, loc, depth, output))
    return true;
  return false;
}

bool Preprocessor::ProcessConditionalDirective(std::string_view line,
                                               uint32_t file_id,
                                               uint32_t line_num,
                                               std::string& output) {
  if (StartsWithDirective(line, "ifdef")) {
    HandleIfdef(AfterDirective(line, "ifdef"), false);
    return true;
  }
  if (StartsWithDirective(line, "ifndef")) {
    HandleIfdef(AfterDirective(line, "ifndef"), true);
    return true;
  }
  if (StartsWithDirective(line, "elsif")) {
    HandleElsif(AfterDirective(line, "elsif"));
    return true;
  }
  if (StartsWithDirective(line, "else")) {
    HandleElse();
    // §22.2: text after `else on same line is preserved.
    if (IsActive()) OutputRemainder(line, "else", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "endif")) {
    HandleEndif();
    // §22.2: text after `endif on same line is preserved.
    if (IsActive()) OutputRemainder(line, "endif", file_id, line_num, output);
    return true;
  }
  return false;
}

}  // namespace delta
