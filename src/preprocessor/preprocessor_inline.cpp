#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/macro_table.h"
#include "preprocessor/preprocessor.h"

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
    bool has_default =
        i < def.param_defaults.size() && def.param_defaults[i] != "\x01";
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

// The text_macro_identifier at the head of `macro_name` (Syntax 22-3): an
// escaped identifier runs to the next white space (5.6.1), and a simple
// identifier is its run of identifier characters (5.6), so whatever follows the
// name -- a parenthesis, a space, a semicolon -- is not part of it.
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
    if (expanding == name) {
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
  // §22.5.1: ExpandMacro expands each argument (before the caller pushes this
  // macro onto the expansion stack), so a same-macro call in an argument is not
  // treated as recursion.
  expanded = ExpandMacro(def, args_text, loc);
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

  expansion_stack_.emplace_back(name);
  // A body opening with a directive the inline expanders do not read, such as
  // `include or `timescale, is a directive line and goes to ProcessDirective.
  // A body holding a conditional compilation directive is not: §22.6 lets
  // `ifdef stand anywhere in the source description (printed page 712), and
  // §22.5.1 has a directive written in a macro's text take effect when the
  // macro is used (printed page 710), so ExpandSubstitutedBody evaluates it.
  auto exp_trimmed = Trim(std::string_view(expanded));
  bool starts_directive = !exp_trimmed.empty() && exp_trimmed[0] == '`' &&
                          !HasInlineConditional(exp_trimmed);
  if (!starts_directive) {
    expanded = ExpandSubstitutedBody(expanded, loc.file_id, loc.line);
  }
  // §22.5.1 (printed page 710): a macro is recursive where it expands to
  // text holding a usage of itself, and the rest of the line its usage
  // stands on is no part of that text, so the macro leaves the expansion
  // stack before the rest is expanded; expanded under it, a second usage on
  // the line, `DO_INCLUDE("a") `DO_INCLUDE("b"), was reported recursive.
  expansion_stack_.pop_back();
  // The rest of the line completes a directive the body opened, `INC "f.svh"
  // after `define INC `include, unless it opens with a backtick of its own:
  // a further directive or a usage expanding to one is a directive of its
  // own and not trailing text of the first, which §22.4 lets only white
  // space or a comment follow.
  std::string_view rest_trimmed = Trim(rest);
  bool rest_is_own_text = !rest_trimmed.empty() && rest_trimmed[0] == '`';
  if (!rest.empty() && !(starts_directive && rest_is_own_text)) {
    expanded += ExpandInlineMacros(rest, loc.file_id, loc.line);
  }
  if (starts_directive) {
    ProcessDirective(expanded, loc.file_id, loc.line, depth, output);
    if (rest_is_own_text)
      output.append(ExpandInlineMacros(rest, loc.file_id, loc.line));
  } else {
    output.append(expanded);
  }
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

// §22.5.1 requires the actual arguments of a usage to be enclosed in
// parentheses and separated by commas, allows white space between the name and
// the left parenthesis, and places none of it on any particular line: a list
// still open at the end of a physical line continues on the next one, and a
// name ending a line has its list on a line after it, §5.3 making the newline
// between them white space. The usage read here is the one the expanders read
// -- the name as ExpandSingleInlineMacro parses it and the list as
// ExtractBalancedArgs finds it -- so a text this answers kComplete for is one
// they expand whole. The list has to open where the expander at the head of a
// line requires it to, at the first character after the name, since a join
// reads lines ahead and a parenthesis further along the line is not one this
// macro's arguments open.
//
// The scan ends at a backtick introducing a compiler directive, because the
// text after one is the directive's operand and not a usage: a `define body in
// particular is arbitrary text, and a list it leaves open is closed by whatever
// usage the body is written to pair with, not by a later line of this file.
// `__FILE__ and `__LINE__ (22.13) stand for a value and are stepped over.
//
// OpensArgumentList is the test ExpandUserDefinedMacro applies to a usage at
// the head of a line: the character after the name, blanks aside, is the list's
// own parenthesis.
static bool OpensArgumentList(std::string_view after_name) {
  size_t open = after_name.find_first_not_of(" \t");
  return open != std::string_view::npos && after_name[open] == '(';
}

MacroUsageEnd Preprocessor::EndOfMacroUsage(std::string_view text) const {
  bool in_string = false;
  size_t pos = FindNextBacktick(text, 0, in_string);
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
    pos = FindNextBacktick(text, pos, in_string);
  }
  return MacroUsageEnd::kComplete;
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
  // §22.5.1: ExpandMacro expands each argument before substitution (and before
  // this macro is pushed below), so a same-macro call in an argument is not
  // treated as recursion; the body re-expansion still guards true recursion.
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
    // §22.5.1: a text-macro usage naming an undefined macro is an error. A
    // compiler directive (e.g. `timescale) that reaches the inline expander is
    // handled elsewhere and is not a macro reference, so it is left verbatim
    // without diagnosis; a conditional compilation directive does not reach
    // here from a macro body, since ExpandSubstitutedBody evaluates it before
    // this expander runs. This branch also catches line-leading undefined
    // macros, which fall through to the inline expander as ordinary text.
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
    // §22.5.1: the parentheses are always required in the usage of a macro
    // defined with arguments. A usage at the head of a line is reported by
    // ExpandUserDefinedMacro; this is the same report for one after other
    // text, which used to be left for the lexer to stumble on.
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

  expansion_stack_.emplace_back(name);
  std::string body = ExpandMacro(*def, {}, loc);
  result += ExpandSubstitutedBody(body, file_id, line_num);
  expansion_stack_.pop_back();
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

// The text a macro's usage substitutes is read the way a source line is: the
// conditional compilation directives first, then the macro usages. §22.6 lets
// `ifdef, `ifndef, `else and `endif stand anywhere in the source description
// (printed page 712), and §22.5.1 has a compiler directive written in a macro's
// text wait until the macro is used, its other macro usages being substituted
// after the outer macro is (printed page 710); so a body such as UVM's
// `if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) ) begin` holds a
// conditional to evaluate at each usage, against the defines in force there.
// The conditionals go first because they choose which of the body's macro
// usages are expanded at all. The three expanders once ran ExpandInlineMacros
// alone on the body, which copied each directive name through as though it
// were a `timescale, and the lexer reported the backtick under §5.2.
std::string Preprocessor::ExpandSubstitutedBody(std::string_view body,
                                                uint32_t file_id,
                                                uint32_t line_num) {
  return ExpandInlineMacros(ExpandInlineConditionals(body), file_id, line_num);
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

// Returns the leading whitespace-delimited word of `trimmed`.
static std::string_view FirstWord(std::string_view trimmed) {
  size_t end = 0;
  while (end < trimmed.size() &&
         !std::isspace(static_cast<unsigned char>(trimmed[end]))) {
    ++end;
  }
  return trimmed.substr(0, end);
}

// True when `rest` opens with the whole word `word`.
static bool StartsWithWord(std::string_view rest, std::string_view word) {
  if (!rest.starts_with(word)) return false;
  return rest.size() == word.size() || !IsIdentChar(rest[word.size()]);
}

// §3.2 names the design elements: module, macromodule, program, interface,
// checker, package, primitive, and configuration. The keyword is matched as
// the line's first word so that any whitespace may separate it from the name
// that follows, and something must follow — a keyword standing alone on a line
// names no element. An interface class is a class rather than an interface —
// it is closed by endclass, not endinterface — so it opens no design element.
static bool IsDesignElementStart(std::string_view trimmed) {
  static constexpr std::string_view kKeywords[] = {
      "module",  "macromodule", "program",   "interface",
      "checker", "package",     "primitive", "config",
  };
  auto word = FirstWord(trimmed);
  bool is_keyword = false;
  for (auto keyword : kKeywords) {
    if (word == keyword) {
      is_keyword = true;
      break;
    }
  }
  if (!is_keyword) return false;

  auto rest = Preprocessor::Trim(trimmed.substr(word.size()));
  if (rest.empty()) return false;
  if (word == "interface" && StartsWithWord(rest, "class")) return false;
  return true;
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

// The module a header line declares, or empty for a header of another design
// element.
static std::string_view DeclaredModuleName(std::string_view trimmed) {
  if (trimmed.starts_with("module ")) {
    return ExtractModuleName(trimmed, "module ");
  }
  if (trimmed.starts_with("macromodule ")) {
    return ExtractModuleName(trimmed, "macromodule ");
  }
  return {};
}

void Preprocessor::TrackDesignElement(std::string_view trimmed) {
  if (IsDesignElementStart(trimmed)) {
    if (in_celldefine_) TrackCellModuleName(trimmed, cell_module_names_);
    // Annex E: each of its directives applies to the modules that follow
    // it, so the decay time, charge strength and delay mode in force at this
    // header are the ones this module takes, whatever a later directive sets.
    auto module_name = DeclaredModuleName(trimmed);
    if (!module_name.empty()) {
      module_directives_.push_back(
          {std::string(module_name), default_decay_time_,
           default_decay_time_infinite_, default_trireg_strength_,
           has_default_trireg_strength_, delay_mode_directive_});
    }
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
    diag_.Error(loc, "redefining compiler directive '" + def.name + "'",
                Subclause("22.5.1"));
    return;
  }

  auto after_name = rest.substr(name_end);
  if (escaped && !after_name.empty() &&
      std::isspace(static_cast<unsigned char>(after_name[0]))) {
    after_name.remove_prefix(1);
  }

  if (!after_name.empty() && after_name[0] == '(') {
    auto close = FindMacroParamListClose(after_name);
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
    // §22.5.2 permits reporting an attempt to remove a macro that was never
    // defined, and stops short of making it an error — so a warning is the
    // strongest report the rule allows. Catching a misspelled name here is
    // the whole point, since removing nothing is otherwise silent.
    //
    // The rule is phrased against macros a `define created. This checks only
    // whether the name is defined at all, which keeps a deliberate `undef of
    // a command-line or predefined macro quiet rather than tracking where
    // each definition came from.
    diag_.Warning(
        loc,
        "`undef of a macro that is not defined: '" + std::string(name) + "'",
        Subclause("22.5.2"));
    return;
  }
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
  auto resolved = ResolveInclude(fn, src_dir);
  if (resolved.empty()) {
    diag_.Error(loc, "cannot find include file '" + std::string(fn) + "'",
                Subclause::None());
    return;
  }
  std::ifstream ifs(resolved);
  if (!ifs) {
    diag_.Error(loc, "cannot open include file '" + resolved + "'",
                Subclause::None());
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
  StripIncludeQuotes(fn, after_close);
  ValidateIncludeTrailing(after_close, diag_, loc);

  if (fn.empty()) {
    diag_.Error(loc, "`include filename is empty", Subclause("22.4"));
    return;
  }

  if (angle_bracket && !fn.empty() && fn[0] == '/') {
    diag_.Error(loc, "absolute path not allowed with angle-bracket `include",
                Subclause("22.4"));
    return;
  }

  ResolveAndReadInclude(fn, loc, depth, output, angle_bracket);
}

}  // namespace delta
