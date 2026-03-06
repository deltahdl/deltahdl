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

static std::string_view Trim(std::string_view s) {
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
static bool HasUnterminatedString(std::string_view body) {
  size_t quotes = 0;
  for (size_t i = 0; i < body.size(); ++i) {
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) ++quotes;
  }
  return quotes % 2 != 0;
}

static bool EndsWithBackslash(std::string_view line) {
  return !line.empty() && line.back() == '\\';
}

// Joins backslash-continued lines into a single string.
// Updates eol/line_num so the main loop skips the continuation lines.
static std::string JoinContinuation(std::string_view src, size_t pos,
                                    size_t& eol, uint32_t& line_num) {
  std::string_view first = src.substr(pos, eol - pos);
  std::string joined(first.substr(0, first.size() - 1));  // Strip trailing '\'

  while (eol < src.size()) {
    size_t next_start = eol + 1;
    size_t next_eol = src.find('\n', next_start);
    if (next_eol == std::string_view::npos) next_eol = src.size();
    std::string_view next_line = src.substr(next_start, next_eol - next_start);
    ++line_num;
    eol = next_eol;
    if (EndsWithBackslash(next_line)) {
      joined.append(next_line.substr(0, next_line.size() - 1));
    } else {
      joined.append(next_line);
      break;
    }
  }
  return joined;
}

static bool StartsWithDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Trim(line);
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
  auto trimmed = Trim(line);
  auto rest = trimmed.substr(1 + dir.size());
  return Trim(rest);
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
          auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
          TrackDesignElement(Trim(expanded));
          output.append(expanded);
        }
      }
      output.push_back('\n');
      pos = eol + 1;
      continue;
    }

    // Join backslash-continued lines for `define directives.
    std::string joined;
    if (StartsWithDirective(line, "define") && EndsWithBackslash(line)) {
      joined = JoinContinuation(src, pos, eol, line_num);
      line = joined;
    }

    bool handled = ProcessDirective(line, file_id, line_num, depth, output);
    if (!handled && IsActive()) {
      auto stripped = StripComments(line, in_block_comment_);
      auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
      TrackDesignElement(Trim(expanded));
      output.append(expanded);
    }
    output.push_back('\n');
    pos = eol + 1;
  }
  return output;
}

// §22.2: Output text that follows a directive with a defined end on the
// same line.  Applies macro expansion and comment stripping.
void Preprocessor::OutputRemainder(std::string_view line,
                                   std::string_view directive, uint32_t file_id,
                                   uint32_t line_num, std::string& output) {
  auto rest = AfterDirective(line, directive);
  if (rest.empty()) return;
  auto stripped = StripComments(rest, in_block_comment_);
  auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  output.append(expanded);
}

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc,
                                         uint32_t file_id, uint32_t line_num,
                                         std::string& output) {
  if (StartsWithDirective(line, "timescale")) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`timescale illegal inside a design element");
      return true;
    }
    HandleTimescale(AfterDirective(line, "timescale"), loc);
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
    HandleDefaultNettype(AfterDirective(line, "default_nettype"), loc);
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
    HandleUnconnectedDrive(AfterDirective(line, "unconnected_drive"), loc);
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
    HandleUndef(AfterDirective(line, "undef"), loc);
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
    HandleBeginKeywords(AfterDirective(line, "begin_keywords"), loc, output);
    return true;
  }
  if (StartsWithDirective(line, "end_keywords") && IsActive()) {
    if (design_element_depth_ > 0) {
      diag_.Error(loc, "`end_keywords illegal inside a design element");
      return true;
    }
    HandleEndKeywords(loc, output);
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
        i < def.param_defaults.size() && !def.param_defaults[i].empty();
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
  auto space_pos = macro_name.find_first_of(" \t(");
  auto name = (space_pos != std::string_view::npos)
                  ? macro_name.substr(0, space_pos)
                  : macro_name;

  // Predefined macros (IEEE 1800-2023 §22.13).
  if (TryPredefinedMacro(name, output, file_id, line_num)) return true;

  const auto* def = macros_.Lookup(name);
  if (def == nullptr) return false;

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
  while (i < line.size() && IsIdentChar(line[i])) ++i;
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
    i += balanced.size();
  }
  result += ExpandMacro(*def, args_text);
  return i;
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
  while (name_end < rest.size() && IsIdentChar(rest[name_end])) ++name_end;

  MacroDef def;
  def.def_loc = loc;
  if (name_end == 0) return;

  def.name = std::string(rest.substr(0, name_end));

  // §22.5.1: All compiler directives are predefined; redefining is illegal.
  if (IsCompilerDirective(def.name)) {
    diag_.Error(loc, "redefining compiler directive '" + def.name + "'");
    return;
  }

  auto after_name = rest.substr(name_end);

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

// --- Ifdef expression evaluator (IEEE 1800-2023 §22.6) ---
// Grammar: expr       ::= equiv_expr
//          equiv_expr ::= impl_expr ('<->' impl_expr)*
//          impl_expr  ::= or_expr ('->' or_expr)*
//          or_expr    ::= and_expr ('||' and_expr)*
//          and_expr   ::= unary ('&&' unary)*
//          unary      ::= '!' unary | '(' expr ')' | identifier

static void SkipSpaces(std::string_view& s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s[0]))) {
    s.remove_prefix(1);
  }
}

bool Preprocessor::EvalIfdefExpr(std::string_view expr) {
  auto e = Trim(expr);
  return EvalIfdefEquiv(e);
}

bool Preprocessor::EvalIfdefEquiv(std::string_view& expr) {
  bool result = EvalIfdefImpl(expr);
  SkipSpaces(expr);
  while (expr.size() >= 3 && expr[0] == '<' && expr[1] == '-' &&
         expr[2] == '>') {
    expr.remove_prefix(3);
    bool rhs = EvalIfdefImpl(expr);
    result = (result == rhs);
    SkipSpaces(expr);
  }
  return result;
}

bool Preprocessor::EvalIfdefImpl(std::string_view& expr) {
  bool result = EvalIfdefOr(expr);
  SkipSpaces(expr);
  while (expr.size() >= 2 && expr[0] == '-' && expr[1] == '>') {
    expr.remove_prefix(2);
    bool rhs = EvalIfdefOr(expr);
    result = !result || rhs;
    SkipSpaces(expr);
  }
  return result;
}

bool Preprocessor::EvalIfdefOr(std::string_view& expr) {
  bool result = EvalIfdefAnd(expr);
  SkipSpaces(expr);
  while (expr.size() >= 2 && expr[0] == '|' && expr[1] == '|') {
    expr.remove_prefix(2);
    result = EvalIfdefAnd(expr) || result;
    SkipSpaces(expr);
  }
  return result;
}

bool Preprocessor::EvalIfdefAnd(std::string_view& expr) {
  bool result = EvalIfdefUnary(expr);
  SkipSpaces(expr);
  while (expr.size() >= 2 && expr[0] == '&' && expr[1] == '&') {
    expr.remove_prefix(2);
    result = EvalIfdefUnary(expr) && result;
    SkipSpaces(expr);
  }
  return result;
}

bool Preprocessor::EvalIfdefUnary(std::string_view& expr) {
  SkipSpaces(expr);
  if (!expr.empty() && expr[0] == '!') {
    expr.remove_prefix(1);
    return !EvalIfdefUnary(expr);
  }
  if (!expr.empty() && expr[0] == '(') {
    expr.remove_prefix(1);
    bool result = EvalIfdefEquiv(expr);
    SkipSpaces(expr);
    if (!expr.empty() && expr[0] == ')') expr.remove_prefix(1);
    return result;
  }
  // Identifier.
  SkipSpaces(expr);
  size_t len = 0;
  while (len < expr.size() && IsIdentChar(expr[len])) ++len;
  auto id = expr.substr(0, len);
  expr.remove_prefix(len);
  return macros_.IsDefined(id);
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

std::string Preprocessor::ExpandMacro(const MacroDef& macro,
                                      std::string_view args_text) {
  if (!macro.is_function_like) return macro.body;
  auto args = SplitMacroArgs(args_text);
  // Apply defaults for empty arguments (IEEE §22.5.1).
  std::vector<std::string> resolved;
  resolved.reserve(macro.params.size());
  for (size_t i = 0; i < macro.params.size(); ++i) {
    std::string_view arg = (i < args.size()) ? args[i] : std::string_view{};
    if (arg.empty() && i < macro.param_defaults.size() &&
        !macro.param_defaults[i].empty()) {
      resolved.emplace_back(macro.param_defaults[i]);
    } else {
      resolved.emplace_back(arg);
    }
  }
  std::vector<std::string_view> resolved_views;
  resolved_views.reserve(resolved.size());
  for (const auto& s : resolved) resolved_views.emplace_back(s);
  return SubstituteParams(macro.body, macro.params, resolved_views);
}

// --- Macro helper functions ---

std::vector<std::string> Preprocessor::ParseMacroParams(
    std::string_view param_list, std::vector<std::string>& defaults) {
  std::vector<std::string> params;
  size_t pos = 0;
  while (pos < param_list.size()) {
    auto comma = param_list.find(',', pos);
    if (comma == std::string_view::npos) comma = param_list.size();
    auto token = Trim(param_list.substr(pos, comma - pos));
    auto eq = token.find('=');
    if (eq != std::string_view::npos) {
      params.emplace_back(Trim(token.substr(0, eq)));
      defaults.emplace_back(Trim(token.substr(eq + 1)));
    } else {
      params.emplace_back(token);
      defaults.emplace_back();  // No default.
    }
    pos = comma + 1;
  }
  return params;
}

std::string_view Preprocessor::ExtractBalancedArgs(std::string_view text) {
  auto open = text.find('(');
  if (open == std::string_view::npos) return {};
  int depth = 0;
  for (size_t i = open; i < text.size(); ++i) {
    if (text[i] == '(') ++depth;
    if (text[i] == ')') --depth;
    if (depth == 0) return text.substr(open, i - open + 1);
  }
  return {};
}

std::vector<std::string_view> Preprocessor::SplitMacroArgs(
    std::string_view args_text) {
  std::vector<std::string_view> args;
  int depth = 0;
  size_t start = 0;
  for (size_t i = 0; i < args_text.size(); ++i) {
    if (args_text[i] == '(') ++depth;
    if (args_text[i] == ')') --depth;
    if (args_text[i] == ',' && depth == 0) {
      args.push_back(Trim(args_text.substr(start, i - start)));
      start = i + 1;
    }
  }
  args.push_back(Trim(args_text.substr(start)));
  return args;
}

// Replace an identifier token with its parameter argument if it matches.
static void SubstituteToken(std::string_view token,
                            const std::vector<std::string>& params,
                            const std::vector<std::string_view>& args,
                            std::string& result) {
  for (size_t p = 0; p < params.size() && p < args.size(); ++p) {
    if (token == params[p]) {
      result.append(args[p]);
      return;
    }
  }
  result.append(token);
}

std::string Preprocessor::SubstituteParams(
    std::string_view body, const std::vector<std::string>& params,
    const std::vector<std::string_view>& args) {
  std::string result;
  result.reserve(body.size());
  size_t i = 0;
  while (i < body.size()) {
    // Handle `\`" — escaped quote in macro string (IEEE §22.5.1).
    if (i + 3 < body.size() && body[i] == '`' && body[i + 1] == '\\' &&
        body[i + 2] == '`' && body[i + 3] == '"') {
      result += "\\\"";
      i += 4;
      continue;
    }
    // Handle `" — macro string delimiter (IEEE §22.5.1).
    if (i + 1 < body.size() && body[i] == '`' && body[i + 1] == '"') {
      result += '"';
      i += 2;
      continue;
    }
    // Handle `` (double backtick) concatenation (IEEE §22.5.1).
    if (i + 1 < body.size() && body[i] == '`' && body[i + 1] == '`') {
      i += 2;  // Skip both backticks — concatenate adjacent tokens.
      continue;
    }
    if (!IsIdentChar(body[i])) {
      result += body[i++];
      continue;
    }
    size_t start = i;
    while (i < body.size() && IsIdentChar(body[i])) ++i;
    SubstituteToken(body.substr(start, i - start), params, args, result);
  }
  return result;
}

// Directive handlers moved to preprocessor_directives.cpp.

}  // namespace delta
