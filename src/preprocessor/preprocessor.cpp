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
static bool IsCompilerDirective(std::string_view name) {
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

// §22.5.1: Check for unterminated string literals in macro bodies.
// Handles triple-quoted strings (""") and `" (backtick-quote) delimiters.
static bool HasUnterminatedString(std::string_view body) {
  bool in_string = false;
  bool in_triple = false;
  for (size_t i = 0; i < body.size(); ++i) {
    // Skip `" (backtick-quote) — it's a macro string delimiter, not a
    // real string.
    if (body[i] == '`' && i + 1 < body.size() && body[i + 1] == '"') {
      i += 1;
      continue;
    }
    // Skip `\`" (backtick-escaped-quote).
    if (body[i] == '`' && i + 3 < body.size() && body[i + 1] == '\\' &&
        body[i + 2] == '`' && body[i + 3] == '"') {
      i += 3;
      continue;
    }
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
      if (in_triple) {
        if (i + 2 < body.size() && body[i + 1] == '"' && body[i + 2] == '"') {
          in_triple = false;
          i += 2;
        }
      } else if (in_string) {
        in_string = false;
      } else if (i + 2 < body.size() && body[i + 1] == '"' &&
                 body[i + 2] == '"') {
        in_triple = true;
        i += 2;
      } else {
        in_string = true;
      }
    }
  }
  return in_string || in_triple;
}

static bool IsIdentChar(char c);

static bool EndsWithBackslash(std::string_view line) {
  return !line.empty() && line.back() == '\\';
}

// Count unmatched triple-quote sequences in text (ignoring inside comments).
static bool HasOpenTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 2 < text.size(); ++i) {
    if (text[i] == '"' && text[i + 1] == '"' && text[i + 2] == '"') {
      ++count;
      i += 2;
    }
  }
  return count % 2 != 0;
}

// Check for an unclosed block comment in text.
static bool HasOpenBlockComment(std::string_view text) {
  bool in_string = false;
  bool in_block = false;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] == '"' && (i == 0 || text[i - 1] != '\\') &&
        (i == 0 || text[i - 1] != '`')) {
      if (!in_block) in_string = !in_string;
      continue;
    }
    if (in_string) continue;
    if (!in_block && i + 1 < text.size() && text[i] == '/' &&
        text[i + 1] == '*') {
      in_block = true;
      ++i;
    } else if (in_block && i + 1 < text.size() && text[i] == '*' &&
               text[i + 1] == '/') {
      in_block = false;
      ++i;
    }
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
      if (i + 1 < line.size() && line[i] == '*' && line[i + 1] == '/') {
        result += "*/";
        i += 2;
        in_block_comment = false;
      } else {
        result += ' ';
        ++i;
      }
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

    // Line comment: replace remainder with spaces.
    if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '/') {
      result += "//";
      i += 2;
      while (i < line.size()) {
        result += ' ';
        ++i;
      }
      return result;
    }

    // Block comment start.
    if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '*') {
      result += "/*";
      i += 2;
      in_block_comment = true;
      continue;
    }

    result += line[i++];
  }
  return result;
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
    if (eol == std::string_view::npos) {
      eol = src.size();
    }
    std::string_view line = src.substr(pos, eol - pos);
    ++line_num;

    // §22.2: Handle block comments spanning multiple lines.
    if (in_block_comment_) {
      auto close = line.find("*/");
      if (close == std::string_view::npos) {
        // Entire line is inside block comment; pass through as-is.
        output.append(line);
        output.push_back('\n');
        pos = eol + 1;
        continue;
      }
      // Block comment ends on this line. Pass the comment portion through,
      // then process the remainder after */.
      output.append(line.substr(0, close + 2));
      in_block_comment_ = false;
      auto remainder = line.substr(close + 2);
      // Process remainder as a new (virtual) line.
      if (!Trim(remainder).empty()) {
        bool handled =
            ProcessDirective(remainder, file_id, line_num, depth, output);
        if (!handled && IsActive()) {
          auto stripped = StripComments(remainder, in_block_comment_);
          auto conditioned = ExpandInlineConditionals(stripped);
          auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
          TrackDesignElement(Trim(expanded));
          output.append(expanded);
        }
      }
      output.push_back('\n');
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
      auto stripped = StripComments(line, in_block_comment_);
      // §22.6: Expand inline `ifdef/`ifndef...`endif before macro expansion.
      auto conditioned = ExpandInlineConditionals(stripped);
      auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
      TrackDesignElement(Trim(expanded));
      output.append(expanded);
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

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc,
                                         uint32_t file_id, uint32_t line_num,
                                         std::string& output) {
  if (StartsWithDirective(line, "timescale")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`timescale illegal inside a design element");
      return true;
    }
    auto rest = AfterDirective(line, "timescale");
    // §22.2: Macro expansion shall occur within a compiler directive.
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [ts_arg, remainder] = SplitTimescaleArg(expanded);
    HandleTimescale(ts_arg, loc);
    // §22.2: text after the directive's defined end is preserved.
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "resetall")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`resetall illegal inside a design element");
      return true;
    }
    // §22.3: `resetall does NOT affect text macros, `line, or
    // `begin_keywords/`end_keywords.
    default_net_type_ = NetType::kWire;
    in_celldefine_ = false;
    unconnected_drive_ = NetType::kWire;
    has_timescale_ = false;
    current_timescale_ = TimeScale{};
    // Annex E: reset optional directive state.
    default_decay_time_ = 0;
    default_decay_time_real_ = 0.0;
    default_decay_time_infinite_ = true;
    default_trireg_strength_ = 0;
    has_default_trireg_strength_ = false;
    delay_mode_directive_ = DelayModeDirective::kNone;
    OutputRemainder(line, "resetall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "default_nettype")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`default_nettype illegal inside a design element");
      return true;
    }
    auto rest = AfterDirective(line, "default_nettype");
    // §22.2: Macro expansion shall occur within a compiler directive.
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleDefaultNettype(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
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
  if (StartsWithDirective(line, "nounconnected_drive")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`nounconnected_drive illegal inside a design element");
      return true;
    }
    unconnected_drive_ = NetType::kWire;
    OutputRemainder(line, "nounconnected_drive", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "unconnected_drive")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`unconnected_drive illegal inside a design element");
      return true;
    }
    auto rest = AfterDirective(line, "unconnected_drive");
    // §22.2: Macro expansion shall occur within a compiler directive.
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleUnconnectedDrive(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "pragma")) {
    // §22.11: pragma_name is required after `pragma.
    auto rest = Trim(AfterDirective(line, "pragma"));
    if (rest.empty()) {
      diag_.Error(loc, "`pragma requires a pragma_name");
    }
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  // --- Annex E: optional compiler directives ---
  if (StartsWithDirective(line, "default_decay_time")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`default_decay_time illegal inside a design element");
      return true;
    }
    HandleDefaultDecayTime(AfterDirective(line, "default_decay_time"), loc);
    return true;
  }
  if (StartsWithDirective(line, "default_trireg_strength")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc,
                  "`default_trireg_strength illegal inside a design element");
      return true;
    }
    HandleDefaultTriregStrength(AfterDirective(line, "default_trireg_strength"),
                                loc);
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_distributed")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc,
                  "`delay_mode_distributed illegal inside a design element");
      return true;
    }
    delay_mode_directive_ = DelayModeDirective::kDistributed;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_path")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`delay_mode_path illegal inside a design element");
      return true;
    }
    delay_mode_directive_ = DelayModeDirective::kPath;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_unit")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`delay_mode_unit illegal inside a design element");
      return true;
    }
    delay_mode_directive_ = DelayModeDirective::kUnit;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_zero")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`delay_mode_zero illegal inside a design element");
      return true;
    }
    delay_mode_directive_ = DelayModeDirective::kZero;
    return true;
  }
  return false;
}

bool Preprocessor::ProcessDirective(std::string_view line, uint32_t file_id,
                                    uint32_t line_num, int depth,
                                    std::string& output) {
  auto trimmed = Trim(line);
  if (trimmed.empty()) return false;
  if (trimmed[0] != '`') return false;
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
    auto rest = AfterDirective(line, "undef");
    auto trimmed_rest = Trim(rest);
    // Extract just the macro name identifier (or escaped identifier).
    size_t name_end = 0;
    if (!trimmed_rest.empty() && trimmed_rest[0] == '\\') {
      // §22.5.1: Escaped identifier — ends at first whitespace.
      name_end = 1;
      while (name_end < trimmed_rest.size() &&
             !std::isspace(static_cast<unsigned char>(trimmed_rest[name_end])))
        ++name_end;
    } else {
      while (name_end < trimmed_rest.size() &&
             IsIdentChar(trimmed_rest[name_end]))
        ++name_end;
    }
    HandleUndef(trimmed_rest.substr(0, name_end), loc);
    // §22.2: text after the directive's defined end is preserved.
    if (IsActive()) {
      auto remainder = Trim(trimmed_rest.substr(name_end));
      OutputText(remainder, file_id, line_num, output);
    }
    return true;
  }
  if (ProcessConditionalDirective(line, file_id, line_num, output)) return true;
  if (StartsWithDirective(line, "include") && IsActive()) {
    auto inc_arg = AfterDirective(line, "include");
    // §22.4: expand macros in include argument before processing.
    auto expanded_arg = ExpandInlineMacros(inc_arg, file_id, line_num);
    // Determine bracket type before stripping quotes.
    auto trimmed_arg = Trim(std::string_view(expanded_arg));
    bool angle_bracket = !trimmed_arg.empty() && trimmed_arg.front() == '<';
    HandleInclude(expanded_arg, loc, depth, output, angle_bracket);
    return true;
  }
  if (StartsWithDirective(line, "begin_keywords") && IsActive()) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`begin_keywords illegal inside a design element");
      return true;
    }
    auto rest = AfterDirective(line, "begin_keywords");
    auto [bk_arg, remainder] = SplitQuotedArg(rest);
    HandleBeginKeywords(bk_arg, loc, output);
    // §22.2: text after the directive's defined end is preserved.
    OutputText(remainder, file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "end_keywords") && IsActive()) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`end_keywords illegal inside a design element");
      return true;
    }
    HandleEndKeywords(loc, output);
    // §22.2: text after the directive's defined end is preserved.
    OutputRemainder(line, "end_keywords", file_id, line_num, output);
    return true;
  }
  if (IsActive() && ProcessStateDirective(line, loc, file_id, line_num, output))
    return true;
  // Check for macro invocation: `MACRO_NAME
  if (IsActive() && TryExpandMacro(trimmed, output, file_id, line_num, depth)) {
    return true;
  }
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

// §22.5.1: Validate that all required macro args are provided.
bool Preprocessor::ValidateMacroArgCount(const MacroDef& def,
                                         std::string_view args_text,
                                         SourceLoc loc, std::string_view name) {
  auto args = SplitMacroArgs(args_text);
  if (args.size() > def.params.size()) {
    diag_.Error(loc,
                "too many arguments for macro '" + std::string(name) + "'");
    return false;
  }
  for (size_t i = args.size(); i < def.params.size(); ++i) {
    bool has_default =
        i < def.param_defaults.size() && def.param_defaults[i] != "\x01";
    if (!has_default) {
      diag_.Error(loc,
                  "too few arguments for macro '" + std::string(name) + "'");
      return false;
    }
  }
  return true;
}

bool Preprocessor::TryPredefinedMacro(std::string_view name,
                                      std::string& output, uint32_t file_id,
                                      uint32_t line_num) {
  if (name == "__FILE__") {
    output.append("\"");
    if (has_line_override_ && !line_file_override_.empty()) {
      output.append(line_file_override_);
    } else {
      output.append(src_mgr_.FilePath(file_id));
    }
    output.append("\"");
    return true;
  }
  if (name == "__LINE__") {
    uint32_t effective_line = line_num;
    if (has_line_override_) {
      effective_line = line_offset_ + (line_num - line_override_src_line_);
    }
    output.append(std::to_string(effective_line));
    return true;
  }
  return false;
}

bool Preprocessor::TryExpandMacro(std::string_view trimmed, std::string& output,
                                  uint32_t file_id, uint32_t line_num,
                                  int depth) {
  auto macro_name = trimmed.substr(1);
  std::string_view name;
  if (!macro_name.empty() && macro_name[0] == '\\') {
    // §22.5.1: Escaped identifier — name ends at first whitespace.
    auto ws = macro_name.find_first_of(" \t");
    name =
        (ws != std::string_view::npos) ? macro_name.substr(0, ws) : macro_name;
  } else {
    auto space_pos = macro_name.find_first_of(" \t(");
    name = (space_pos != std::string_view::npos)
               ? macro_name.substr(0, space_pos)
               : macro_name;
  }

  // Predefined macros (IEEE 1800-2023 §22.13).
  if (TryPredefinedMacro(name, output, file_id, line_num)) return true;

  const auto* def = macros_.Lookup(name);
  if (def == nullptr) return false;

  // §22.5.1: Parentheses always required for function-like macros.
  if (def->is_function_like) {
    auto after_name = Trim(macro_name.substr(name.size()));
    if (after_name.empty() || after_name[0] != '(') {
      diag_.Error({file_id, line_num, 1},
                  "parentheses required for function-like macro '" +
                      std::string(name) + "'");
      return true;
    }
  }

  // §22.5.1: Detect recursive macro expansion.
  for (const auto& expanding : expansion_stack_) {
    if (expanding == name) {
      diag_.Error({file_id, line_num, 1},
                  "recursive expansion of macro '" + std::string(name) + "'");
      return true;
    }
  }

  std::string expanded;
  std::string_view rest;
  if (def->is_function_like) {
    auto after_name = macro_name.substr(name.size());
    auto balanced = ExtractBalancedArgs(after_name);
    if (balanced.empty()) return false;
    auto args_text = balanced.substr(1, balanced.size() - 2);
    if (!ValidateMacroArgCount(*def, args_text, {file_id, line_num, 1}, name)) {
      return false;
    }
    expanded = ExpandMacro(*def, args_text);
    auto end_pos = static_cast<size_t>(balanced.data() + balanced.size() -
                                       after_name.data());
    rest = after_name.substr(end_pos);
  } else {
    expanded = ExpandMacro(*def, {});
    rest = macro_name.substr(name.size());
  }
  // §22.5.1: Push macro onto expansion stack for recursion detection.
  expansion_stack_.emplace_back(name);

  // Append remaining text and expand further inline macros.
  if (!rest.empty()) {
    expanded += ExpandInlineMacros(rest, file_id, line_num);
  }
  // §22.5.1: rescan expansion for directives (e.g., `include from macro).
  auto exp_trimmed = Trim(std::string_view(expanded));
  if (!exp_trimmed.empty() && exp_trimmed[0] == '`') {
    ProcessDirective(expanded, file_id, line_num, depth, output);
  } else {
    output.append(expanded);
  }

  expansion_stack_.pop_back();
  return true;
}

static bool IsIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
}

// Find the next backtick outside a string literal, starting at pos.
// Returns npos if not found.  Updates in_string tracking.
static size_t FindNextBacktick(std::string_view line, size_t pos,
                               bool& in_string) {
  for (size_t i = pos; i < line.size(); ++i) {
    if (line[i] == '"' && (i == 0 || line[i - 1] != '\\')) {
      in_string = !in_string;
    }
    if (!in_string && line[i] == '`') return i;
  }
  return std::string_view::npos;
}

// Expand a single inline macro at position `pos` (pointing at the backtick).
// Appends expansion to `result` and returns the position after the macro.
// If the backtick is not a valid macro, appends the literal text and returns
// the position just past the backtick.
size_t Preprocessor::ExpandSingleInlineMacro(std::string_view line, size_t pos,
                                             uint32_t file_id,
                                             uint32_t line_num,
                                             std::string& result) {
  size_t i = pos + 1;  // skip backtick
  size_t name_start = i;
  if (i < line.size() && line[i] == '\\') {
    // §22.5.1: Escaped identifier macro name.
    ++i;
    while (i < line.size() &&
           !std::isspace(static_cast<unsigned char>(line[i])))
      ++i;
  } else {
    while (i < line.size() && IsIdentChar(line[i])) ++i;
  }
  if (i == name_start) {
    result += '`';
    return pos + 1;
  }
  auto name = line.substr(name_start, i - name_start);

  if (name == "__FILE__") {
    result += '"';
    if (has_line_override_ && !line_file_override_.empty()) {
      result += line_file_override_;
    } else {
      result += src_mgr_.FilePath(file_id);
    }
    result += '"';
    return i;
  }
  if (name == "__LINE__") {
    uint32_t effective = line_num;
    if (has_line_override_) {
      effective = line_offset_ + (line_num - line_override_src_line_);
    }
    result += std::to_string(effective);
    return i;
  }

  const auto* def = macros_.Lookup(name);
  if (def == nullptr) {
    result.append(line.substr(pos, i - pos));
    return i;
  }

  // §22.5.1: Detect recursive macro expansion.
  for (const auto& expanding : expansion_stack_) {
    if (expanding == name) {
      diag_.Error({file_id, line_num, 1},
                  "recursive expansion of macro '" + std::string(name) + "'");
      result.append(line.substr(pos, i - pos));
      return i;
    }
  }

  std::string_view args_text;
  if (def->is_function_like) {
    auto rest = line.substr(i);
    auto balanced = ExtractBalancedArgs(rest);
    if (balanced.empty()) {
      result.append(line.substr(pos, i - pos));
      return i;
    }
    args_text = balanced.substr(1, balanced.size() - 2);
    if (!ValidateMacroArgCount(*def, args_text, {file_id, line_num, 1}, name)) {
      result.append(line.substr(pos, i - pos));
      return i;
    }
    // Advance past everything up to and including the closing paren.
    i += static_cast<size_t>(balanced.data() + balanced.size() - rest.data());
  }
  expansion_stack_.emplace_back(name);
  result += ExpandMacro(*def, args_text);
  expansion_stack_.pop_back();
  return i;
}

// §22.6: Find a `ifdef or `ifndef that is followed by a matching `endif
// on the same line. Returns npos if none found.
static bool MatchesDirective(std::string_view text, std::string_view dir) {
  if (text.size() < 1 + dir.size()) return false;
  if (text[0] != '`') return false;
  if (text.substr(1, dir.size()) != dir) return false;
  if (text.size() > 1 + dir.size() && IsIdentChar(text[1 + dir.size()]))
    return false;
  return true;
}

static size_t FindInlineConditional(std::string_view line) {
  for (size_t i = 0; i < line.size(); ++i) {
    if (line[i] != '`') continue;
    auto rest = line.substr(i);
    bool is_ifdef = MatchesDirective(rest, "ifdef");
    bool is_ifndef = MatchesDirective(rest, "ifndef");
    if (!is_ifdef && !is_ifndef) continue;

    // Check if there's a matching `endif on the same line.
    size_t dir_len = is_ifndef ? 7 : 6;
    int depth = 1;
    for (size_t j = i + dir_len; j < line.size(); ++j) {
      if (line[j] != '`') continue;
      auto jr = line.substr(j);
      if (MatchesDirective(jr, "ifdef") || MatchesDirective(jr, "ifndef")) {
        ++depth;
      } else if (MatchesDirective(jr, "endif")) {
        --depth;
        if (depth == 0) return i;
      }
    }
  }
  return std::string_view::npos;
}

// §22.6: Process inline `ifdef/`ifndef...`else...`endif within a line.
std::string Preprocessor::ExpandInlineConditionals(std::string_view line) {
  std::string result(line);

  while (true) {
    size_t ifdef_pos = FindInlineConditional(result);
    if (ifdef_pos == std::string::npos) break;

    auto rest = std::string_view(result).substr(ifdef_pos);
    bool is_ifndef = MatchesDirective(rest, "ifndef");
    size_t dir_len = is_ifndef ? 7 : 6;

    // Extract condition.
    size_t cond_start = ifdef_pos + dir_len;
    while (cond_start < result.size() &&
           std::isspace(static_cast<unsigned char>(result[cond_start])))
      ++cond_start;

    size_t cond_end;
    bool has_expr = (cond_start < result.size() && result[cond_start] == '(');
    if (has_expr) {
      int pdepth = 0;
      cond_end = cond_start;
      for (; cond_end < result.size(); ++cond_end) {
        if (result[cond_end] == '(') ++pdepth;
        if (result[cond_end] == ')') {
          --pdepth;
          if (pdepth == 0) {
            ++cond_end;
            break;
          }
        }
      }
    } else {
      cond_end = cond_start;
      while (cond_end < result.size() && IsIdentChar(result[cond_end]))
        ++cond_end;
    }

    auto condition =
        std::string_view(result).substr(cond_start, cond_end - cond_start);
    bool cond_result;
    if (has_expr) {
      cond_result = EvalIfdefExpr(condition);
    } else {
      cond_result = macros_.IsDefined(condition);
    }
    if (is_ifndef) cond_result = !cond_result;

    // Find `else and `endif at depth 0 within this inline conditional.
    size_t else_pos = std::string::npos;
    size_t endif_pos = std::string::npos;
    int depth = 1;
    for (size_t j = cond_end; j < result.size(); ++j) {
      if (result[j] != '`') continue;
      auto jr = std::string_view(result).substr(j);
      if (MatchesDirective(jr, "ifdef") || MatchesDirective(jr, "ifndef")) {
        ++depth;
      } else if (MatchesDirective(jr, "endif")) {
        --depth;
        if (depth == 0) {
          endif_pos = j;
          break;
        }
      } else if (depth == 1 && MatchesDirective(jr, "else")) {
        if (else_pos == std::string::npos) else_pos = j;
      }
    }

    if (endif_pos == std::string::npos) break;

    // Extract the appropriate block.
    std::string replacement;
    if (cond_result) {
      size_t text_end = (else_pos != std::string::npos) ? else_pos : endif_pos;
      replacement = result.substr(cond_end, text_end - cond_end);
    } else if (else_pos != std::string::npos) {
      replacement = result.substr(else_pos + 5, endif_pos - (else_pos + 5));
    }

    // Replace the `ifdef...`endif span.
    size_t span_end = endif_pos + 6;
    result =
        result.substr(0, ifdef_pos) + replacement + result.substr(span_end);
  }

  return result;
}

std::string Preprocessor::ExpandInlineMacros(std::string_view line,
                                             uint32_t file_id,
                                             uint32_t line_num) {
  bool in_string = false;
  size_t first = FindNextBacktick(line, 0, in_string);
  if (first == std::string_view::npos) return std::string(line);

  std::string result;
  result.reserve(line.size());
  size_t copied = 0;
  in_string = false;  // reset for second pass

  while (true) {
    size_t bt = FindNextBacktick(line, copied, in_string);
    if (bt == std::string_view::npos) break;
    result.append(line.substr(copied, bt - copied));
    copied = ExpandSingleInlineMacro(line, bt, file_id, line_num, result);
  }
  result.append(line.substr(copied));
  return result;
}

bool Preprocessor::IsActive() const {
  return std::all_of(cond_stack_.begin(), cond_stack_.end(),
                     [](const CondState& s) { return s.active; });
}

// §3.2 + §22.3: Track design element nesting for resetall validation.
// A design element is a module, program, interface, checker, package,
// primitive, or configuration.
void Preprocessor::TrackDesignElement(std::string_view trimmed) {
  if (trimmed.starts_with("module ") || trimmed.starts_with("program ") ||
      trimmed.starts_with("interface ") || trimmed.starts_with("checker ") ||
      trimmed.starts_with("package ") || trimmed.starts_with("primitive ") ||
      trimmed.starts_with("config ") || trimmed.starts_with("macromodule ")) {
    ++design_element_depth_;
  }
  // Also check for end keywords anywhere in the line (handles single-line
  // declarations like "module m; endmodule").
  if (trimmed.find("endmodule") != std::string_view::npos ||
      trimmed.find("endprogram") != std::string_view::npos ||
      trimmed.find("endinterface") != std::string_view::npos ||
      trimmed.find("endchecker") != std::string_view::npos ||
      trimmed.find("endpackage") != std::string_view::npos ||
      trimmed.find("endprimitive") != std::string_view::npos ||
      trimmed.find("endconfig") != std::string_view::npos) {
    if (design_element_depth_ > 0) --design_element_depth_;
  }
}

// §22.5.1: Strip comments from macro body text.
// Line comments (// ...) are removed entirely.
// Block comments (/* ... */) are removed entirely.
// Comments inside string literals or `" regions are preserved.
static std::string StripMacroBodyComments(std::string_view body) {
  std::string result;
  result.reserve(body.size());
  bool in_string = false;
  size_t i = 0;

  while (i < body.size()) {
    // Track string literals (skip \" escapes).
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
      // Check for `" (backtick-quote) — not a real string delimiter.
      if (i > 0 && body[i - 1] == '`') {
        result += body[i++];
        continue;
      }
      in_string = !in_string;
      result += body[i++];
      continue;
    }

    if (in_string) {
      result += body[i++];
      continue;
    }

    // Line comment: remove remainder.
    if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '/') {
      break;
    }

    // Block comment: remove entirely.
    if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '*') {
      i += 2;
      while (i + 1 < body.size() && !(body[i] == '*' && body[i + 1] == '/')) {
        ++i;
      }
      if (i + 1 < body.size()) i += 2;  // Skip */
      continue;
    }

    result += body[i++];
  }
  // Trim trailing whitespace left after comment removal.
  while (!result.empty() &&
         std::isspace(static_cast<unsigned char>(result.back()))) {
    result.pop_back();
  }
  return result;
}

void Preprocessor::HandleDefine(std::string_view rest, SourceLoc loc) {
  if (!IsActive()) return;

  // Find where the macro name ends.
  size_t name_end = 0;
  bool escaped = false;
  if (!rest.empty() && rest[0] == '\\') {
    // §22.5.1: Escaped identifier macro name.
    escaped = true;
    name_end = 1;
    while (name_end < rest.size() &&
           !std::isspace(static_cast<unsigned char>(rest[name_end])))
      ++name_end;
  } else {
    while (name_end < rest.size() && IsIdentChar(rest[name_end])) ++name_end;
  }

  MacroDef def;
  def.def_loc = loc;
  if (name_end == 0) return;

  def.name = std::string(rest.substr(0, name_end));

  // §22.5.1: All compiler directives are predefined; redefining is illegal.
  if (!escaped && IsCompilerDirective(def.name)) {
    diag_.Error(loc, "redefining compiler directive '" + def.name + "'");
    return;
  }

  auto after_name = rest.substr(name_end);
  // §22.5.1: Escaped identifier requires single whitespace before (.
  if (escaped && !after_name.empty() &&
      std::isspace(static_cast<unsigned char>(after_name[0]))) {
    after_name.remove_prefix(1);
  }

  // Function-like: `( immediately after name, NO space (IEEE §22.5.1).
  if (!after_name.empty() && after_name[0] == '(') {
    auto close = after_name.find(')');
    if (close != std::string_view::npos) {
      def.is_function_like = true;
      def.params =
          ParseMacroParams(after_name.substr(1, close - 1), def.param_defaults);
      def.body = StripMacroBodyComments(Trim(after_name.substr(close + 1)));
    }
  } else {
    def.body = StripMacroBodyComments(Trim(after_name));
  }
  if (HasUnterminatedString(def.body)) {
    diag_.Error(loc, "unterminated string literal in macro body");
    return;
  }

  macros_.Define(std::move(def));
}

void Preprocessor::HandleUndef(std::string_view rest, SourceLoc /*loc*/) {
  if (!IsActive()) return;
  auto name = Trim(rest);
  macros_.Undefine(name);
}

static bool IsIfdefExpr(std::string_view text) {
  return !text.empty() && (text[0] == '(' || text[0] == '!');
}

void Preprocessor::HandleIfdef(std::string_view rest, bool inverted) {
  auto name = Trim(rest);
  bool cond = IsIfdefExpr(name) ? EvalIfdefExpr(name) : macros_.IsDefined(name);
  if (inverted) cond = !cond;
  bool parent = IsActive();
  bool active = parent && cond;
  cond_stack_.push_back({active, active, parent});
}

void Preprocessor::HandleElsif(std::string_view rest) {
  if (cond_stack_.empty()) return;
  auto& top = cond_stack_.back();
  auto name = Trim(rest);
  bool defined =
      IsIfdefExpr(name) ? EvalIfdefExpr(name) : macros_.IsDefined(name);
  top.active = top.parent_active && !top.any_taken && defined;
  if (top.active) top.any_taken = true;
}

void Preprocessor::HandleElse() {
  if (cond_stack_.empty()) return;
  auto& top = cond_stack_.back();
  top.active = top.parent_active && !top.any_taken;
  top.any_taken = true;
}

void Preprocessor::HandleEndif() {
  if (!cond_stack_.empty()) {
    cond_stack_.pop_back();
  }
}

void Preprocessor::HandleInclude(std::string_view filename_raw, SourceLoc loc,
                                 int depth, std::string& output,
                                 bool angle_bracket) {
  auto fn = Trim(filename_raw);
  if (fn.empty()) {
    diag_.Error(loc, "`include requires a filename");
    return;
  }
  // Strip quotes properly: find matching closing " or >.
  std::string_view after_close;
  if (fn.size() >= 2 && (fn.front() == '"' || fn.front() == '<')) {
    char close = (fn.front() == '"') ? '"' : '>';
    auto end = fn.find(close, 1);
    if (end != std::string_view::npos) {
      after_close = Trim(fn.substr(end + 1));
      fn = fn.substr(1, end - 1);
    } else {
      fn = fn.substr(1, fn.size() - 2);
    }
  }

  // §22.4: Only whitespace or a comment may follow the include filename.
  if (!after_close.empty() &&
      !(after_close.size() >= 2 && after_close[0] == '/' &&
        (after_close[1] == '/' || after_close[1] == '*'))) {
    diag_.Error(loc,
                "only whitespace or a comment may follow `include filename");
  }

  if (fn.empty()) {
    diag_.Error(loc, "`include filename is empty");
    return;
  }

  // §22.4: Absolute paths are only allowed with the double-quote form.
  if (angle_bracket && !fn.empty() && fn[0] == '/') {
    diag_.Error(loc, "absolute path not allowed with angle-bracket `include");
    return;
  }

  // §22.4: Double-quote form searches source dir then include_dirs.
  // Angle-bracket form searches only include_dirs.
  auto src_path = src_mgr_.FilePath(loc.file_id);
  std::string src_dir;
  if (!angle_bracket) {
    auto slash = src_path.rfind('/');
    if (slash != std::string_view::npos) {
      src_dir = std::string(src_path.substr(0, slash));
    }
  }
  auto resolved = ResolveInclude(fn, src_dir);
  if (resolved.empty()) {
    diag_.Error(loc, "cannot find include file '" + std::string(fn) + "'");
    return;
  }
  std::ifstream ifs(resolved);
  if (!ifs) {
    diag_.Error(loc, "cannot open include file '" + resolved + "'");
    return;
  }
  std::ostringstream ss;
  ss << ifs.rdbuf();
  auto content = ss.str();
  auto inc_id = src_mgr_.AddFile(resolved, content);
  output.append(ProcessSource(content, inc_id, depth + 1));
}

// Ifdef evaluator and macro helpers in preprocessor_macros.cpp.
// Directive handlers in preprocessor_directives.cpp.

}  // namespace delta
