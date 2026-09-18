#include <cctype>

#include "preprocessor/preprocessor.h"

namespace delta {

bool IsIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$';
}

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

  SkipSpaces(expr);
  size_t len = 0;
  while (len < expr.size() && IsIdentChar(expr[len])) ++len;
  auto id = expr.substr(0, len);
  expr.remove_prefix(len);
  return macros_.IsDefined(id);
}

std::string Preprocessor::ExpandMacro(const MacroDef& macro,
                                      std::string_view args_text,
                                      SourceLoc loc) {
  if (!macro.is_function_like) return macro.body;
  auto args = SplitMacroArgs(args_text);

  std::vector<std::string> resolved;
  resolved.reserve(macro.params.size());
  for (size_t i = 0; i < macro.params.size(); ++i) {
    std::string_view arg = (i < args.size()) ? args[i] : std::string_view{};
    if (arg.empty() && i < macro.param_defaults.size() &&
        macro.param_defaults[i] != "\x01") {
      resolved.emplace_back(macro.param_defaults[i]);
    } else {
      // §22.5.1: an actual argument is macro-expanded before being substituted
      // for the formal argument. Splitting happens first, on the raw text, so
      // the argument count and default selection are decided before expansion
      // (an argument expanding to empty, e.g. `EMPTY, is a provided-but-empty
      // argument, not an omitted one). Expanding here -- before the caller
      // pushes this macro onto the expansion stack -- also means an argument
      // that calls the same macro is not mistaken for a recursive expansion.
      resolved.emplace_back(ExpandInlineMacros(arg, loc.file_id, loc.line));
    }
  }
  std::vector<std::string_view> resolved_views;
  resolved_views.reserve(resolved.size());
  for (const auto& s : resolved) resolved_views.emplace_back(s);
  return SubstituteParams(macro.body, macro.params, resolved_views);
}

// Whether the three characters at `i` are a triple quote, which opens or
// closes A.8.8's triple_quoted_string.
static bool AtTripleQuote(std::string_view text, size_t i) {
  return text.substr(i, 3) == "\"\"\"";
}

// The index after the escaped identifier (5.6.1) opening at text[i], which
// runs from its backslash to the next white space.
static size_t EndOfEscapedIdentifier(std::string_view text, size_t i) {
  while (i < text.size() &&
         !std::isspace(static_cast<unsigned char>(text[i]))) {
    ++i;
  }
  return i;
}

// Tracks the matched pairs §22.5.1 lists -- parentheses, square brackets,
// braces, double quotes, triple quotes and an escaped identifier -- so that a
// comma or right parenthesis inside one of them is not read as an argument
// separator or the end of the list. Read consumes what stands at text[i] -- a
// delimiter, one item of a string, or a whole escaped identifier -- and returns
// the index of the next character to read; `inside` reports whether text[i]
// stood inside a string, a triple-quoted string or an escaped identifier, where
// a comma or parenthesis is text rather than punctuation.
struct DelimiterTracker {
  int paren_depth = 0;
  int bracket_depth = 0;
  int brace_depth = 0;
  bool in_string = false;
  bool in_triple = false;

  // One item of an open string, or the quote that closes it. A '"' that a
  // backslash precedes is 5.9's escape sequence inside a quoted_string and
  // closes nothing; a lone '"' inside a triple_quoted_string is an item of it
  // (A.8.8), and only a `"""` closes it.
  size_t ReadStringItem(std::string_view text, size_t i) {
    if (in_triple) {
      if (!AtTripleQuote(text, i)) return i + 1;
      in_triple = false;
      return i + 3;
    }
    if (text[i] == '"' && text[i - 1] != '\\') in_string = false;
    return i + 1;
  }

  void Nest(char c) {
    if (c == '(')
      ++paren_depth;
    else if (c == ')')
      --paren_depth;
    else if (c == '[')
      ++bracket_depth;
    else if (c == ']')
      --bracket_depth;
    else if (c == '{')
      ++brace_depth;
    else if (c == '}')
      --brace_depth;
  }

  size_t Read(std::string_view text, size_t i, bool& inside) {
    inside = true;
    if (in_triple || in_string) return ReadStringItem(text, i);
    if (text[i] == '\\') return EndOfEscapedIdentifier(text, i);
    if (AtTripleQuote(text, i)) {
      in_triple = true;
      return i + 3;
    }
    if (text[i] == '"') {
      in_string = true;
      return i + 1;
    }
    inside = false;
    Nest(text[i]);
    return i + 1;
  }

  bool AtTopLevel() const {
    return paren_depth == 0 && bracket_depth == 0 && brace_depth == 0;
  }
};

// Records one formal parameter token ("name" or "name = default") into params
// and defaults; a missing default is stored as the "\x01" sentinel, an empty
// one (name =) as the empty string.
static void AppendMacroParam(std::string_view token,
                             std::vector<std::string>& params,
                             std::vector<std::string>& defaults) {
  auto trimmed = Preprocessor::Trim(token);
  // The formal argument name is a simple_identifier (22.5.1), so the first '='
  // is always the boundary between the name and its default text.
  auto eq = trimmed.find('=');
  if (eq != std::string_view::npos) {
    params.emplace_back(Preprocessor::Trim(trimmed.substr(0, eq)));
    defaults.emplace_back(Preprocessor::Trim(trimmed.substr(eq + 1)));
  } else {
    params.emplace_back(trimmed);
    defaults.emplace_back("\x01");
  }
}

std::vector<std::string> Preprocessor::ParseMacroParams(
    std::string_view param_list, std::vector<std::string>& defaults) {
  std::vector<std::string> params;
  DelimiterTracker tracker;
  size_t start = 0;
  size_t i = 0;
  while (i < param_list.size()) {
    // §22.5.1: a default may contain a comma inside a matched pair or an
    // escaped identifier; such commas do not separate formal parameters.
    bool inside = false;
    size_t next = tracker.Read(param_list, i, inside);
    if (!inside && param_list[i] == ',' && tracker.AtTopLevel()) {
      AppendMacroParam(param_list.substr(start, i - start), params, defaults);
      start = i + 1;
    }
    i = next;
  }
  AppendMacroParam(param_list.substr(start), params, defaults);
  return params;
}

size_t Preprocessor::FindMacroParamListClose(std::string_view text) {
  DelimiterTracker tracker;
  size_t i = 0;
  while (i < text.size()) {
    bool inside = false;
    size_t next = tracker.Read(text, i, inside);
    // The list's own '(' is the sole reason paren_depth is nonzero; the first
    // ')' that returns every delimiter to top level (and is not inside a
    // string or an escaped identifier) closes the parameter list.
    if (!inside && text[i] == ')' && tracker.AtTopLevel()) return i;
    i = next;
  }
  return std::string_view::npos;
}

// The actual argument list opening at the first '(' of `text`, parentheses
// included, or empty when the list is not closed within `text`. §22.5.1 lists
// the matched pairs a right parenthesis is protected inside, so the ')' that
// closes the list is the first one standing at top level of every pair.
std::string_view Preprocessor::ExtractBalancedArgs(std::string_view text) {
  auto open = text.find('(');
  if (open == std::string_view::npos) return {};
  DelimiterTracker tracker;
  size_t i = open;
  while (i < text.size()) {
    bool inside = false;
    size_t next = tracker.Read(text, i, inside);
    if (!inside && text[i] == ')' && tracker.AtTopLevel()) {
      return text.substr(open, i - open + 1);
    }
    i = next;
  }
  return {};
}

std::vector<std::string_view> Preprocessor::SplitMacroArgs(
    std::string_view args_text) {
  std::vector<std::string_view> args;
  DelimiterTracker tracker;
  size_t start = 0;
  size_t i = 0;
  while (i < args_text.size()) {
    // §22.5.1: a comma inside a matched pair or an escaped identifier (5.6.1)
    // is part of the argument, not a separator.
    bool inside = false;
    size_t next = tracker.Read(args_text, i, inside);
    if (!inside && args_text[i] == ',' && tracker.AtTopLevel()) {
      args.push_back(Trim(args_text.substr(start, i - start)));
      start = i + 1;
    }
    i = next;
  }
  args.push_back(Trim(args_text.substr(start)));
  return args;
}

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

// Handles the macro-quote escape sequences (`\`", `", and ``) at body[i],
// appending their literal expansion to result. Returns the number of source
// characters consumed, or 0 if no macro-quote begins at body[i].
static size_t AppendMacroQuote(std::string_view body, size_t i,
                               std::string& result) {
  if (i + 3 < body.size() && body[i] == '`' && body[i + 1] == '\\' &&
      body[i + 2] == '`' && body[i + 3] == '"') {
    result += "\\\"";
    return 4;
  }
  if (i + 1 < body.size() && body[i] == '`' && body[i + 1] == '"') {
    result += '"';
    return 2;
  }
  if (i + 1 < body.size() && body[i] == '`' && body[i + 1] == '`') {
    return 2;
  }
  return 0;
}

// §22.5.1: macro and argument substitution shall not occur within string
// literals. Copies one literal character (honoring escapes) at body[i] into
// result, clearing in_string at the closing quote. Returns chars consumed.
static size_t CopyStringChar(std::string_view body, size_t i, bool& in_string,
                             std::string& result) {
  if (body[i] == '\\' && i + 1 < body.size()) {
    result += body[i];
    result += body[i + 1];
    return 2;
  }
  if (body[i] == '"') in_string = false;
  result += body[i];
  return 1;
}

std::string Preprocessor::SubstituteParams(
    std::string_view body, const std::vector<std::string>& params,
    const std::vector<std::string_view>& args) {
  std::string result;
  result.reserve(body.size());
  size_t i = 0;
  bool in_string = false;
  while (i < body.size()) {
    if (in_string) {
      i += CopyStringChar(body, i, in_string, result);
      continue;
    }
    // The `" macro-quote does not start a suppression region: its contents are
    // meant to be substituted, unlike a plain " string literal.
    if (size_t consumed = AppendMacroQuote(body, i, result)) {
      i += consumed;
      continue;
    }
    if (!IsIdentChar(body[i])) {
      if (body[i] == '"') in_string = true;
      result += body[i++];
      continue;
    }
    size_t start = i;
    while (i < body.size() && IsIdentChar(body[i])) ++i;
    SubstituteToken(body.substr(start, i - start), params, args, result);
  }
  return result;
}

}  // namespace delta
