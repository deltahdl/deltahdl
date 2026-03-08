#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>

#include "preprocessor/preprocessor.h"

namespace delta {

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
