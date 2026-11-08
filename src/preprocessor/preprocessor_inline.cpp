#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/macro_table.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

bool Preprocessor::ValidateMacroArgCount(const MacroDef& def,
                                         std::string_view args_text,
                                         SourceLoc loc, std::string_view name) {
  auto args = SplitMacroArgs(args_text);
  if (args.size() > def.params.size()) {
    diag_.Error(loc, "too many arguments for macro '" + std::string(name) + "'",
                Subclause("22.5.1"));
    return false;
  }
  for (size_t i = args.size(); i < def.params.size(); ++i) {
    bool has_default = def.param_defaults[i] != "\x01";
    if (!has_default) {
      diag_.Error(loc,
                  "too few arguments for macro '" + std::string(name) + "'",
                  Subclause("22.5.1"));
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
    if (has_line_override_) {
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
  size_t end = 0;
  while (end < macro_name.size() && IsIdentChar(macro_name[end])) ++end;
  return macro_name.substr(0, end);
}

bool Preprocessor::IsRecursiveExpansion(std::string_view name,
                                        SourceLoc loc) const {
  for (const auto& expanding : expansion_stack_) {
    if (expanding == MacroTable::Key(name)) {
      diag_.Error(loc,
                  "recursive expansion of macro '" + std::string(name) + "'",
                  Subclause("22.5.1"));
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
  expanded = ExpandMacro(def, args_text, loc);
  auto end_pos = static_cast<size_t>(balanced.data() + balanced.size() -
                                     after_name.data());
  rest = after_name.substr(end_pos);
  return true;
}

static bool OpensCompilerDirective(std::string_view text) {
  if (text.empty() || text[0] != '`') return false;
  size_t end = 1;
  while (end < text.size() && IsIdentChar(text[end])) ++end;
  return IsDirectiveOtherThanValue(text.substr(1, end - 1));
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
      diag_.Error(loc,
                  "parentheses required for function-like macro '" +
                      std::string(name) + "'",
                  Subclause("22.5.1"));
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
    expanded = ExpandMacro(*def, {}, loc);
    rest = macro_name.substr(name.size());
  }

  expansion_stack_.emplace_back(def->name);
  auto exp_trimmed = Trim(std::string_view(expanded));
  bool starts_directive =
      OpensCompilerDirective(exp_trimmed) && !HasInlineConditional(exp_trimmed);
  if (starts_directive) {
    RunDirectiveOpenedByMacro(std::move(expanded), rest, loc, depth, output);
    return true;
  }
  expanded = ExpandSubstitutedBody(expanded, loc.file_id, loc.line);
  expansion_stack_.pop_back();
  if (!rest.empty()) {
    expanded += ExpandInlineMacros(rest, loc.file_id, loc.line);
  }
  output.append(expanded);
  return true;
}

void Preprocessor::RunDirectiveOpenedByMacro(std::string expanded,
                                             std::string_view rest,
                                             SourceLoc loc, int depth,
                                             std::string& output) {
  std::string_view rest_trimmed = Trim(rest);
  bool rest_is_own_line = !rest_trimmed.empty() && rest_trimmed[0] == '`';
  if (!rest.empty() && !rest_is_own_line) {
    expanded += ExpandInlineMacros(rest, loc.file_id, loc.line);
  }
  ProcessDirective(expanded, loc.file_id, loc.line, depth, output);
  expansion_stack_.pop_back();
  if (rest_is_own_line &&
      !ProcessDirective(rest_trimmed, loc.file_id, loc.line, depth, output)) {
    output.append(ExpandInlineMacros(rest, loc.file_id, loc.line));
  }
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

static size_t StepOutsideString(std::string_view line, size_t i,
                                StringLiteralState& state) {
  if (line[i] == '\\') {
    state = StringLiteralState::kEscapedIdentifier;
    return i + 1;
  }
  if (line[i] != '"' || (i > 0 && line[i - 1] == '`')) return i + 1;
  if (!AtTripleQuote(line, i)) {
    state = StringLiteralState::kQuoted;
    return i + 1;
  }
  state = StringLiteralState::kTripleQuoted;
  return i + 3;
}

size_t StepOverStringSyntax(std::string_view line, size_t i,
                            StringLiteralState& state) {
  if (state == StringLiteralState::kOutside) {
    return StepOutsideString(line, i, state);
  }
  if (state == StringLiteralState::kEscapedIdentifier) {
    if (std::isspace(static_cast<unsigned char>(line[i]))) {
      state = StringLiteralState::kOutside;
    }
    return i + 1;
  }
  if (line[i] == '\\') return i + 2;
  if (state == StringLiteralState::kQuoted) {
    if (line[i] == '"') state = StringLiteralState::kOutside;
    return i + 1;
  }
  if (!AtTripleQuote(line, i)) return i + 1;
  state = StringLiteralState::kOutside;
  return i + 3;
}

static size_t FindNextBacktick(std::string_view line, size_t pos,
                               StringLiteralState& state) {
  while (pos < line.size()) {
    if (OutsideEveryString(state) && line[pos] == '`') return pos;
    pos = StepOverStringSyntax(line, pos, state);
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

static bool OpensArgumentList(std::string_view after_name) {
  size_t open = after_name.find_first_not_of(" \t");
  return open != std::string_view::npos && after_name[open] == '(';
}

MacroUsageEnd Preprocessor::EndOfMacroUsage(std::string_view text) const {
  auto state = StringLiteralState::kOutside;
  size_t pos = FindNextBacktick(text, 0, state);
  while (pos != std::string_view::npos) {
    size_t name_start = pos + 1;
    size_t name_end = ParseInlineMacroName(text, name_start);
    auto name = text.substr(name_start, name_end - name_start);
    if (IsDirectiveOtherThanValue(name)) return MacroUsageEnd::kComplete;
    pos = name_end;
    const auto* def = macros_.Lookup(name);
    auto after_name = text.substr(name_end);
    bool function_like = def != nullptr && def->is_function_like;
    if (function_like && Trim(after_name).empty()) {
      return MacroUsageEnd::kNameAlone;
    }
    if (function_like && OpensArgumentList(after_name)) {
      auto balanced = ExtractBalancedArgs(after_name);
      if (balanced.empty()) return MacroUsageEnd::kListOpen;
      pos = name_end + static_cast<size_t>(balanced.data() + balanced.size() -
                                           after_name.data());
    }
    pos = FindNextBacktick(text, pos, state);
  }
  return MacroUsageEnd::kComplete;
}

bool Preprocessor::TryExpandInlinePredefined(std::string_view name,
                                             uint32_t file_id,
                                             uint32_t line_num,
                                             std::string& result) {
  if (name == "__FILE__") {
    result += '"';
    if (has_line_override_) {
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
  std::string body = ExpandMacro(def, args_text, loc);
  expansion_stack_.emplace_back(def.name);
  result += ExpandSubstitutedBody(body, loc.file_id, loc.line);
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
    if (!IsCompilerDirective(name)) {
      diag_.Error({file_id, line_num, 1},
                  "undefined macro '" + std::string(name) + "'",
                  Subclause("22.5.1"));
    }
    result.append(line.substr(pos, i - pos));
    return i;
  }

  SourceLoc loc{file_id, line_num, 1};
  if (IsRecursiveExpansion(name, loc)) {
    result.append(line.substr(pos, i - pos));
    return i;
  }

  if (def->is_function_like) {
    if (!OpensArgumentList(line.substr(i))) {
      diag_.Error(loc,
                  "parentheses required for function-like macro '" +
                      std::string(name) + "'",
                  Subclause("22.5.1"));
      result.append(line.substr(pos, i - pos));
      return i;
    }
    size_t advance = ExpandInlineFunctionMacro(*def, line, i, loc, result);
    if (advance == 0) {
      result.append(line.substr(pos, i - pos));
      return i;
    }
    return advance;
  }

  expansion_stack_.emplace_back(def->name);
  std::string body = ExpandMacro(*def, {}, loc);
  result += ExpandSubstitutedBody(body, file_id, line_num);
  expansion_stack_.pop_back();
  return i;
}

std::string Preprocessor::ExpandInlineMacros(std::string_view line,
                                             uint32_t file_id,
                                             uint32_t line_num) {
  auto state = StringLiteralState::kOutside;
  size_t bt = FindNextBacktick(line, 0, state);
  if (bt == std::string_view::npos) return std::string(line);

  std::string result;
  result.reserve(line.size());
  size_t copied = 0;

  while (bt != std::string_view::npos) {
    result.append(line.substr(copied, bt - copied));
    copied = ExpandSingleInlineMacro(line, bt, file_id, line_num, result);
    size_t scan = bt;
    while (scan < copied) scan = StepOverStringSyntax(line, scan, state);
    bt = FindNextBacktick(line, scan, state);
  }
  result.append(line.substr(copied));
  return result;
}

std::string Preprocessor::ExpandSubstitutedBody(std::string_view body,
                                                uint32_t file_id,
                                                uint32_t line_num) {
  return ExpandInlineMacros(
      ExpandInlineConditionals(body, SourceLoc{file_id, line_num, 1}), file_id,
      line_num);
}

bool Preprocessor::IsActive() const {
  return std::all_of(cond_stack_.begin(), cond_stack_.end(),
                     [](const CondState& s) { return s.active; });
}

static bool SkipBlockComment(std::string_view body, size_t& i) {
  i += 2;
  while (i + 1 < body.size() && (body[i] != '*' || body[i + 1] != '/')) {
    ++i;
  }
  if (i + 1 >= body.size()) return false;
  i += 2;
  return true;
}

static bool CopyEscapedIdentifier(std::string_view body, size_t& i,
                                  std::string& result) {
  if (body[i] != '\\' || (i > 0 && body[i - 1] == '`')) return false;
  const size_t kEnd = EndOfEscapedIdentifier(body, i);
  result.append(body.substr(i, kEnd - i));
  i = kEnd;
  return true;
}

static bool ProcessMacroBodyChar(std::string_view body, size_t& i,
                                 bool& in_string, bool& unclosed_comment,
                                 std::string& result) {
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

  if (CopyEscapedIdentifier(body, i, result)) return true;

  if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '/') {
    return false;
  }

  if (i + 1 < body.size() && body[i] == '/' && body[i + 1] == '*') {
    if (!SkipBlockComment(body, i)) unclosed_comment = true;
    result += ' ';
    return true;
  }

  result += body[i++];
  return true;
}

static std::string StripMacroBodyComments(std::string_view body,
                                          bool& unclosed_comment) {
  std::string result;
  result.reserve(body.size());
  bool in_string = false;
  size_t i = 0;

  while (i < body.size()) {
    if (!ProcessMacroBodyChar(body, i, in_string, unclosed_comment, result))
      break;
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
  if (name_end == 0 || (!escaped && rest[0] != '_' &&
                        !std::isalpha(static_cast<unsigned char>(rest[0])))) {
    diag_.Error(loc, "`define is missing its macro name", Subclause("22.5.1"));
    return;
  }

  def.name = std::string(rest.substr(0, name_end));

  if (!escaped && IsCompilerDirective(def.name)) {
    diag_.Error(loc, "redefining compiler directive '" + def.name + "'",
                Subclause("22.5.1"));
    return;
  }

  auto after_name = rest.substr(name_end);
  if (escaped && !after_name.empty()) after_name.remove_prefix(1);

  bool unclosed_comment = false;
  if (!after_name.empty() && after_name[0] == '(') {
    auto close = FindMacroParamListClose(after_name);
    if (close == std::string_view::npos) {
      diag_.Error(
          loc,
          "formal argument list of `define " + def.name + " is never closed",
          Subclause("22.5.1"));
      return;
    }
    def.is_function_like = true;
    def.params =
        ParseMacroParams(after_name.substr(1, close - 1), def.param_defaults);
    def.body = StripMacroBodyComments(Trim(after_name.substr(close + 1)),
                                      unclosed_comment);
  } else {
    def.body = StripMacroBodyComments(Trim(after_name), unclosed_comment);
  }
  if (unclosed_comment) {
    diag_.Error(loc, "unterminated block comment", Subclause("5.4"));
    return;
  }
  if (HasUnterminatedString(def.body)) {
    diag_.Error(loc, "unterminated string literal in macro body",
                Subclause("22.5.1"));
    return;
  }

  macros_.Define(std::move(def));
}

void Preprocessor::HandleUndef(std::string_view rest, SourceLoc loc) {
  if (!IsActive()) return;
  auto name = Trim(rest);
  if (!macros_.IsDefined(name)) {
    diag_.Warning(
        loc,
        "`undef of a macro that is not defined: '" + std::string(name) + "'",
        Subclause("22.5.2"));
    return;
  }
  macros_.Undefine(name);
}

static bool ReportNoOpenConditional(bool none_open, std::string_view directive,
                                    SourceLoc loc, DiagEngine& diag) {
  if (!none_open) return false;
  diag.Error(loc,
             "`" + std::string(directive) +
                 " with no `ifdef or `ifndef open before it",
             Subclause("22.6"));
  return true;
}

void Preprocessor::HandleIfdef(std::string_view rest, bool inverted,
                               SourceLoc loc) {
  bool cond =
      EvalIfdefCondition(Trim(rest), inverted ? "ifndef" : "ifdef", loc);
  if (inverted) cond = !cond;
  bool parent = IsActive();
  bool active = parent && cond;
  cond_stack_.push_back({active, active, parent, loc});
}

void Preprocessor::HandleElsif(std::string_view rest, SourceLoc loc) {
  if (ReportNoOpenConditional(cond_stack_.empty(), "elsif", loc, diag_)) return;
  auto& top = cond_stack_.back();
  bool defined = EvalIfdefCondition(Trim(rest), "elsif", loc);
  top.active = top.parent_active && !top.any_taken && defined;
  if (top.active) top.any_taken = true;
}

void Preprocessor::HandleElse(SourceLoc loc) {
  if (ReportNoOpenConditional(cond_stack_.empty(), "else", loc, diag_)) return;
  auto& top = cond_stack_.back();
  if (top.else_seen) {
    diag_.Error(loc, "a second `else in one `ifdef or `ifndef",
                Subclause("22.6"));
  }
  top.else_seen = true;
  top.active = top.parent_active && !top.any_taken;
  top.any_taken = true;
}

void Preprocessor::HandleEndif(SourceLoc loc) {
  if (ReportNoOpenConditional(cond_stack_.empty(), "endif", loc, diag_)) return;
  cond_stack_.pop_back();
}

void Preprocessor::ReportUnclosedConditionals() {
  for (const CondState& open : cond_stack_) {
    diag_.Error(open.opened, "`ifdef or `ifndef with no closing `endif",
                Subclause("22.6"));
  }
  cond_stack_.clear();
}

static bool StripIncludeQuotes(std::string_view& fn,
                               std::string_view& after_close) {
  after_close = {};
  char close = (fn.front() == '"') ? '"' : '>';
  auto end = fn.find(close, 1);
  if (end == std::string_view::npos) return false;
  after_close = Preprocessor::Trim(fn.substr(end + 1));
  fn = fn.substr(1, end - 1);
  return true;
}

static void ValidateIncludeTrailing(std::string_view after_close,
                                    DiagEngine& diag, SourceLoc loc) {
  if (after_close.empty()) return;
  if (after_close.size() >= 2 && after_close[0] == '/' &&
      (after_close[1] == '/' || after_close[1] == '*'))
    return;
  diag.Error(loc, "only whitespace or a comment may follow `include filename",
             Subclause("22.4"));
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
  auto resolved = ResolveInclude(fn, src_dir, !angle_bracket);
  if (resolved.empty()) {
    diag_.Error(loc, "cannot find include file '" + std::string(fn) + "'",
                Subclause::None());
    return;
  }
  std::ifstream ifs(resolved);
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
    diag_.Error(loc, "`include requires a filename", Subclause("22.4"));
    return;
  }

  if (fn.front() != '"' && fn.front() != '<') {
    diag_.Error(loc,
                "`include filename must be enclosed in double quotes or angle "
                "brackets",
                Subclause("22.4"));
    return;
  }

  std::string_view after_close;
  if (!StripIncludeQuotes(fn, after_close)) {
    diag_.Error(loc,
                std::string("`include file name is missing its closing ") +
                    (fn.front() == '"' ? "\"" : ">"),
                Subclause("22.4"));
    return;
  }
  ValidateIncludeTrailing(after_close, diag_, loc);

  if (fn.empty()) {
    diag_.Error(loc, "`include filename is empty", Subclause("22.4"));
    return;
  }

  if (angle_bracket && fn[0] == '/') {
    diag_.Error(loc, "absolute path not allowed with angle-bracket `include",
                Subclause("22.4"));
    return;
  }

  ResolveAndReadInclude(fn, loc, depth, output, angle_bracket);
}

}  // namespace delta
