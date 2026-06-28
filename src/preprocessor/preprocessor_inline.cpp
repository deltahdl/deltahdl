#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>

#include "preprocessor/preprocessor.h"

namespace delta {

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
      effective_line = line_offset_ + (line_num - line_override_src_line_ - 1);
    }
    output.append(std::to_string(effective_line));
    return true;
  }
  return false;
}

static std::string_view ExtractMacroName(std::string_view macro_name) {
  if (!macro_name.empty() && macro_name[0] == '\\') {
    auto ws = macro_name.find_first_of(" \t");
    return (ws != std::string_view::npos) ? macro_name.substr(0, ws)
                                          : macro_name;
  }
  auto space_pos = macro_name.find_first_of(" \t(");
  return (space_pos != std::string_view::npos) ? macro_name.substr(0, space_pos)
                                               : macro_name;
}

bool Preprocessor::IsRecursiveExpansion(std::string_view name,
                                        SourceLoc loc) const {
  for (const auto& expanding : expansion_stack_) {
    if (expanding == name) {
      diag_.Error(loc,
                  "recursive expansion of macro '" + std::string(name) + "'");
      return true;
    }
  }
  return false;
}

bool Preprocessor::ExpandFunctionLikeMacro(const MacroDef& def,
                                           std::string_view macro_name,
                                           SourceLoc loc, std::string& expanded,
                                           std::string_view& rest) {
  auto name = ExtractMacroName(macro_name);
  auto after_name = macro_name.substr(name.size());
  auto balanced = ExtractBalancedArgs(after_name);
  if (balanced.empty()) return false;
  auto args_text = balanced.substr(1, balanced.size() - 2);
  if (!ValidateMacroArgCount(def, args_text, loc, name)) return false;
  // §22.5.1: macro arguments are expanded before parameter substitution. This
  // runs before the caller pushes def onto the expansion stack, so an argument
  // that calls the same macro -- `TOP(`TOP(b,1), `TOP(42,a)) -- is expanded in
  // the caller's context and is not mistaken for a recursive expansion.
  std::string expanded_args =
      ExpandInlineMacros(args_text, loc.file_id, loc.line);
  expanded = ExpandMacro(def, expanded_args);
  auto end_pos = static_cast<size_t>(balanced.data() + balanced.size() -
                                     after_name.data());
  rest = after_name.substr(end_pos);
  return true;
}

bool Preprocessor::ExpandUserDefinedMacro(std::string_view name,
                                          std::string_view macro_name,
                                          std::string& output, SourceLoc loc,
                                          int depth) {
  const auto* def = macros_.Lookup(name);
  if (def == nullptr) return false;

  if (def->is_function_like) {
    auto after_name = Trim(macro_name.substr(name.size()));
    if (after_name.empty() || after_name[0] != '(') {
      diag_.Error(loc, "parentheses required for function-like macro '" +
                           std::string(name) + "'");
      return true;
    }
  }

  if (IsRecursiveExpansion(name, loc)) return true;

  std::string expanded;
  std::string_view rest;
  if (def->is_function_like) {
    if (!ExpandFunctionLikeMacro(*def, macro_name, loc, expanded, rest))
      return false;
  } else {
    expanded = ExpandMacro(*def, {});
    rest = macro_name.substr(name.size());
  }

  expansion_stack_.emplace_back(name);
  auto exp_trimmed = Trim(std::string_view(expanded));
  bool starts_directive = !exp_trimmed.empty() && exp_trimmed[0] == '`';
  if (!starts_directive) {
    expanded = ExpandInlineMacros(expanded, loc.file_id, loc.line);
  }
  if (!rest.empty()) {
    expanded += ExpandInlineMacros(rest, loc.file_id, loc.line);
  }
  if (starts_directive) {
    ProcessDirective(expanded, loc.file_id, loc.line, depth, output);
  } else {
    output.append(expanded);
  }

  expansion_stack_.pop_back();
  return true;
}

bool Preprocessor::TryExpandMacro(std::string_view trimmed, std::string& output,
                                  uint32_t file_id, uint32_t line_num,
                                  int depth) {
  auto macro_name = trimmed.substr(1);
  auto name = ExtractMacroName(macro_name);

  if (TryPredefinedMacro(name, output, file_id, line_num)) {
    auto rest = macro_name.substr(name.size());
    if (!rest.empty()) {
      output.append(ExpandInlineMacros(rest, file_id, line_num));
    }
    return true;
  }

  SourceLoc loc{file_id, line_num, 1};
  return ExpandUserDefinedMacro(name, macro_name, output, loc, depth);
}

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

static size_t ParseInlineMacroName(std::string_view line, size_t name_start) {
  size_t i = name_start;
  if (i < line.size() && line[i] == '\\') {
    ++i;
    while (i < line.size() &&
           !std::isspace(static_cast<unsigned char>(line[i])))
      ++i;
  } else {
    while (i < line.size() && IsIdentChar(line[i])) ++i;
  }
  return i;
}

bool Preprocessor::TryExpandInlinePredefined(std::string_view name,
                                             uint32_t file_id,
                                             uint32_t line_num,
                                             std::string& result) {
  if (name == "__FILE__") {
    result += '"';
    if (has_line_override_ && !line_file_override_.empty()) {
      result += line_file_override_;
    } else {
      result += src_mgr_.FilePath(file_id);
    }
    result += '"';
    return true;
  }
  if (name == "__LINE__") {
    uint32_t effective = line_num;
    if (has_line_override_) {
      effective = line_offset_ + (line_num - line_override_src_line_ - 1);
    }
    result += std::to_string(effective);
    return true;
  }
  return false;
}

size_t Preprocessor::ExpandInlineFunctionMacro(const MacroDef& def,
                                               std::string_view line,
                                               size_t name_end, SourceLoc loc,
                                               std::string& result) {
  auto rest = line.substr(name_end);
  auto balanced = ExtractBalancedArgs(rest);
  if (balanced.empty()) return 0;
  auto args_text = balanced.substr(1, balanced.size() - 2);
  if (!ValidateMacroArgCount(def, args_text, loc, def.name)) return 0;
  size_t advance =
      name_end +
      static_cast<size_t>(balanced.data() + balanced.size() - rest.data());
  // §22.5.1: actual macro arguments are themselves subject to macro expansion
  // before being substituted for the formal arguments in the macro text. The
  // arguments are expanded in the caller's context, so the macro is not yet on
  // the expansion stack: a call to the same macro inside an argument (e.g.
  // `TOP(`TOP(b,1), ...)) is not a recursive expansion. Only guard the body.
  std::string expanded_args =
      ExpandInlineMacros(args_text, loc.file_id, loc.line);
  std::string body = ExpandMacro(def, expanded_args);
  expansion_stack_.emplace_back(def.name);
  result += ExpandInlineMacros(body, loc.file_id, loc.line);
  expansion_stack_.pop_back();
  return advance;
}

size_t Preprocessor::ExpandSingleInlineMacro(std::string_view line, size_t pos,
                                             uint32_t file_id,
                                             uint32_t line_num,
                                             std::string& result) {
  size_t name_start = pos + 1;
  size_t i = ParseInlineMacroName(line, name_start);
  if (i == name_start) {
    result += '`';
    return pos + 1;
  }
  auto name = line.substr(name_start, i - name_start);

  if (TryExpandInlinePredefined(name, file_id, line_num, result)) return i;

  const auto* def = macros_.Lookup(name);
  if (def == nullptr) {
    result.append(line.substr(pos, i - pos));
    return i;
  }

  SourceLoc loc{file_id, line_num, 1};
  if (IsRecursiveExpansion(name, loc)) {
    result.append(line.substr(pos, i - pos));
    return i;
  }

  if (def->is_function_like) {
    size_t advance = ExpandInlineFunctionMacro(*def, line, i, loc, result);
    if (advance == 0) {
      result.append(line.substr(pos, i - pos));
      return i;
    }
    return advance;
  }

  expansion_stack_.emplace_back(name);
  std::string body = ExpandMacro(*def, {});
  result += ExpandInlineMacros(body, file_id, line_num);
  expansion_stack_.pop_back();
  return i;
}

static bool MatchesDirective(std::string_view text, std::string_view dir) {
  if (text.size() < 1 + dir.size()) return false;
  if (text[0] != '`') return false;
  if (text.substr(1, dir.size()) != dir) return false;
  if (text.size() > 1 + dir.size() && IsIdentChar(text[1 + dir.size()]))
    return false;
  return true;
}

static bool HasMatchingEndif(std::string_view line, size_t search_start) {
  int depth = 1;
  for (size_t j = search_start; j < line.size(); ++j) {
    if (line[j] != '`') continue;
    auto jr = line.substr(j);
    if (MatchesDirective(jr, "ifdef") || MatchesDirective(jr, "ifndef")) {
      ++depth;
    } else if (MatchesDirective(jr, "endif")) {
      --depth;
      if (depth == 0) return true;
    }
  }
  return false;
}

static size_t FindInlineConditional(std::string_view line) {
  bool in_string = false;
  for (size_t i = 0; i < line.size(); ++i) {
    // A directive sequence sitting inside a string literal is hidden and must
    // not start an inline conditional expansion (22.6).
    if (line[i] == '"' && (i == 0 || line[i - 1] != '\\')) {
      in_string = !in_string;
      continue;
    }
    if (in_string || line[i] != '`') continue;
    auto rest = line.substr(i);
    bool is_ifdef = MatchesDirective(rest, "ifdef");
    bool is_ifndef = MatchesDirective(rest, "ifndef");
    if (!is_ifdef && !is_ifndef) continue;

    size_t dir_len = is_ifndef ? 7 : 6;
    if (HasMatchingEndif(line, i + dir_len)) return i;
  }
  return std::string_view::npos;
}

bool Preprocessor::HasInlineConditional(std::string_view line) const {
  return FindInlineConditional(line) != std::string_view::npos;
}

static size_t SkipWhitespace(const std::string& s, size_t pos) {
  while (pos < s.size() && std::isspace(static_cast<unsigned char>(s[pos])))
    ++pos;
  return pos;
}

static size_t ParseParenthesizedCondition(const std::string& result,
                                          size_t start) {
  int pdepth = 0;
  for (size_t i = start; i < result.size(); ++i) {
    if (result[i] == '(') ++pdepth;
    if (result[i] == ')') {
      --pdepth;
      if (pdepth == 0) return i + 1;
    }
  }
  return result.size();
}

static size_t ParseInlineCondition(const std::string& result, size_t cond_start,
                                   bool& has_expr) {
  has_expr = (cond_start < result.size() && result[cond_start] == '(');
  if (has_expr) return ParseParenthesizedCondition(result, cond_start);
  size_t cond_end = cond_start;
  while (cond_end < result.size() && IsIdentChar(result[cond_end])) ++cond_end;
  return cond_end;
}

struct InlineCondBounds {
  size_t else_pos;
  size_t endif_pos;
};

static InlineCondBounds FindElseAndEndif(const std::string& result,
                                         size_t search_start) {
  size_t else_pos = std::string::npos;
  size_t endif_pos = std::string::npos;
  int depth = 1;
  for (size_t j = search_start; j < result.size(); ++j) {
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
  return {else_pos, endif_pos};
}

static std::string SelectConditionalBlock(const std::string& result,
                                          bool cond_result, size_t cond_end,
                                          size_t else_pos, size_t endif_pos) {
  if (cond_result) {
    size_t text_end = (else_pos != std::string::npos) ? else_pos : endif_pos;
    return result.substr(cond_end, text_end - cond_end);
  }
  if (else_pos != std::string::npos) {
    return result.substr(else_pos + 5, endif_pos - (else_pos + 5));
  }
  return {};
}

std::string Preprocessor::ExpandInlineConditionals(std::string_view line) {
  std::string result(line);

  while (true) {
    size_t ifdef_pos = FindInlineConditional(result);
    if (ifdef_pos == std::string::npos) break;

    auto rest = std::string_view(result).substr(ifdef_pos);
    bool is_ifndef = MatchesDirective(rest, "ifndef");
    size_t dir_len = is_ifndef ? 7 : 6;

    size_t cond_start = SkipWhitespace(result, ifdef_pos + dir_len);

    bool has_expr = false;
    size_t cond_end = ParseInlineCondition(result, cond_start, has_expr);

    auto condition =
        std::string_view(result).substr(cond_start, cond_end - cond_start);
    bool cond_result =
        has_expr ? EvalIfdefExpr(condition) : macros_.IsDefined(condition);
    if (is_ifndef) cond_result = !cond_result;

    auto bounds = FindElseAndEndif(result, cond_end);
    if (bounds.endif_pos == std::string::npos) break;

    auto replacement = SelectConditionalBlock(
        result, cond_result, cond_end, bounds.else_pos, bounds.endif_pos);

    size_t span_end = bounds.endif_pos + 6;
    result.erase(ifdef_pos, span_end - ifdef_pos);
    result.insert(ifdef_pos, replacement);
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

  while (true) {
    // Recalculate in_string based on quote characters from the start of the
    // line to the current copied position. This ensures we correctly track
    // whether we are inside a string literal before searching for the next
    // backtick.
    in_string = false;
    for (size_t i = 0; i < copied && i < line.size(); ++i) {
      if (line[i] == '"' && (i == 0 || line[i - 1] != '\\')) {
        in_string = !in_string;
      }
    }

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

static std::string_view ExtractModuleName(std::string_view trimmed,
                                          std::string_view keyword) {
  auto rest = trimmed.substr(keyword.size());

  if (rest.starts_with("automatic ")) rest = rest.substr(10);
  while (!rest.empty() && (rest[0] == ' ' || rest[0] == '\t'))
    rest.remove_prefix(1);
  size_t end = 0;
  while (end < rest.size() && rest[end] != ' ' && rest[end] != '\t' &&
         rest[end] != '(' && rest[end] != ';' && rest[end] != '#')
    ++end;
  return rest.substr(0, end);
}

static bool IsDesignElementStart(std::string_view trimmed) {
  return trimmed.starts_with("module ") || trimmed.starts_with("program ") ||
         trimmed.starts_with("interface ") || trimmed.starts_with("checker ") ||
         trimmed.starts_with("package ") || trimmed.starts_with("primitive ") ||
         trimmed.starts_with("config ") || trimmed.starts_with("macromodule ");
}

static bool IsDesignElementEnd(std::string_view trimmed) {
  return trimmed.find("endmodule") != std::string_view::npos ||
         trimmed.find("endprogram") != std::string_view::npos ||
         trimmed.find("endinterface") != std::string_view::npos ||
         trimmed.find("endchecker") != std::string_view::npos ||
         trimmed.find("endpackage") != std::string_view::npos ||
         trimmed.find("endprimitive") != std::string_view::npos ||
         trimmed.find("endconfig") != std::string_view::npos;
}

static void TrackCellModuleName(std::string_view trimmed,
                                std::vector<std::string>& cell_module_names) {
  if (trimmed.starts_with("module ")) {
    auto name = ExtractModuleName(trimmed, "module ");
    if (!name.empty()) cell_module_names.emplace_back(name);
  } else if (trimmed.starts_with("macromodule ")) {
    auto name = ExtractModuleName(trimmed, "macromodule ");
    if (!name.empty()) cell_module_names.emplace_back(name);
  }
}

void Preprocessor::TrackDesignElement(std::string_view trimmed) {
  if (IsDesignElementStart(trimmed)) {
    if (in_celldefine_) TrackCellModuleName(trimmed, cell_module_names_);
    ++design_element_depth_;
  }

  if (IsDesignElementEnd(trimmed)) {
    if (design_element_depth_ > 0) --design_element_depth_;
  }
}

static void SkipBlockComment(std::string_view body, size_t& i) {
  i += 2;
  while (i + 1 < body.size() && (body[i] != '*' || body[i + 1] != '/')) {
    ++i;
  }
  if (i + 1 < body.size()) i += 2;
}

static bool ProcessMacroBodyChar(std::string_view body, size_t& i,
                                 bool& in_string, std::string& result) {
  if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
    if (i > 0 && body[i - 1] == '`') {
      result += body[i++];
      return true;
    }
    in_string = !in_string;
    result += body[i++];
    return true;
  }

  if (in_string) {
    result += body[i++];
    return true;
  }

  if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '/') {
    return false;
  }

  if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '*') {
    SkipBlockComment(body, i);
    return true;
  }

  result += body[i++];
  return true;
}

static std::string StripMacroBodyComments(std::string_view body) {
  std::string result;
  result.reserve(body.size());
  bool in_string = false;
  size_t i = 0;

  while (i < body.size()) {
    if (!ProcessMacroBodyChar(body, i, in_string, result)) break;
  }

  while (!result.empty() &&
         std::isspace(static_cast<unsigned char>(result.back()))) {
    result.pop_back();
  }
  return result;
}

static size_t ParseDefineName(std::string_view rest, bool& escaped) {
  size_t name_end = 0;
  escaped = false;
  if (!rest.empty() && rest[0] == '\\') {
    escaped = true;
    name_end = 1;
    while (name_end < rest.size() &&
           !std::isspace(static_cast<unsigned char>(rest[name_end])))
      ++name_end;
  } else {
    while (name_end < rest.size() && IsIdentChar(rest[name_end])) ++name_end;
  }
  return name_end;
}

void Preprocessor::HandleDefine(std::string_view rest, SourceLoc loc) {
  if (!IsActive()) return;

  bool escaped = false;
  size_t name_end = ParseDefineName(rest, escaped);

  MacroDef def;
  def.def_loc = loc;
  if (name_end == 0) return;

  def.name = std::string(rest.substr(0, name_end));

  if (!escaped && IsCompilerDirective(def.name)) {
    diag_.Error(loc, "redefining compiler directive '" + def.name + "'");
    return;
  }

  auto after_name = rest.substr(name_end);
  if (escaped && !after_name.empty() &&
      std::isspace(static_cast<unsigned char>(after_name[0]))) {
    after_name.remove_prefix(1);
  }

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

void Preprocessor::HandleUndef(std::string_view rest, SourceLoc) {
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

static void StripIncludeQuotes(std::string_view& fn,
                               std::string_view& after_close) {
  after_close = {};
  if (fn.size() < 2) return;
  if (fn.front() != '"' && fn.front() != '<') return;
  char close = (fn.front() == '"') ? '"' : '>';
  auto end = fn.find(close, 1);
  if (end != std::string_view::npos) {
    after_close = Preprocessor::Trim(fn.substr(end + 1));
    fn = fn.substr(1, end - 1);
  } else {
    fn = fn.substr(1, fn.size() - 2);
  }
}

static void ValidateIncludeTrailing(std::string_view after_close,
                                    DiagEngine& diag, SourceLoc loc) {
  if (after_close.empty()) return;
  if (after_close.size() >= 2 && after_close[0] == '/' &&
      (after_close[1] == '/' || after_close[1] == '*'))
    return;
  diag.Error(loc, "only whitespace or a comment may follow `include filename");
}

void Preprocessor::ResolveAndReadInclude(std::string_view fn, SourceLoc loc,
                                         int depth, std::string& output,
                                         bool angle_bracket) {
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

void Preprocessor::HandleInclude(std::string_view filename_raw, SourceLoc loc,
                                 int depth, std::string& output,
                                 bool angle_bracket) {
  auto fn = Trim(filename_raw);
  if (fn.empty()) {
    diag_.Error(loc, "`include requires a filename");
    return;
  }

  if (fn.front() != '"' && fn.front() != '<') {
    diag_.Error(loc,
                "`include filename must be enclosed in double quotes or angle "
                "brackets");
    return;
  }

  std::string_view after_close;
  StripIncludeQuotes(fn, after_close);
  ValidateIncludeTrailing(after_close, diag_, loc);

  if (fn.empty()) {
    diag_.Error(loc, "`include filename is empty");
    return;
  }

  if (angle_bracket && !fn.empty() && fn[0] == '/') {
    diag_.Error(loc, "absolute path not allowed with angle-bracket `include");
    return;
  }

  ResolveAndReadInclude(fn, loc, depth, output, angle_bracket);
}

}  // namespace delta
