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

// Tracks nesting of the matched delimiter pairs (22.5.1) — parentheses, square
// brackets, braces, and double-quoted strings — so a comma or right parenthesis
// inside one of them is not treated as a separator or list terminator.
struct DelimiterTracker {
  int paren_depth = 0;
  int bracket_depth = 0;
  int brace_depth = 0;
  bool in_string = false;

  bool Update(char c, char prev) {
    if (c == '"' && prev != '\\') {
      in_string = !in_string;
      return true;
    }
    if (in_string) return true;
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
    return false;
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
  for (size_t i = 0; i < param_list.size(); ++i) {
    // §22.5.1: a default may contain a comma inside a matched pair or an
    // escaped identifier; such commas do not separate formal parameters. Skip
    // an escaped identifier (runs to the next white space) whole.
    if (!tracker.in_string && param_list[i] == '\\') {
      while (i < param_list.size() &&
             !std::isspace(static_cast<unsigned char>(param_list[i]))) {
        ++i;
      }
      --i;
      continue;
    }
    char prev = (i == 0) ? '\0' : param_list[i - 1];
    if (tracker.Update(param_list[i], prev)) continue;
    if (param_list[i] == ',' && tracker.AtTopLevel()) {
      AppendMacroParam(param_list.substr(start, i - start), params, defaults);
      start = i + 1;
    }
  }
  AppendMacroParam(param_list.substr(start), params, defaults);
  return params;
}

size_t Preprocessor::FindMacroParamListClose(std::string_view text) {
  DelimiterTracker tracker;
  for (size_t i = 0; i < text.size(); ++i) {
    if (!tracker.in_string && text[i] == '\\') {
      while (i < text.size() &&
             !std::isspace(static_cast<unsigned char>(text[i]))) {
        ++i;
      }
      --i;
      continue;
    }
    char prev = (i == 0) ? '\0' : text[i - 1];
    tracker.Update(text[i], prev);
    // The list's own '(' is the sole reason paren_depth is nonzero; the first
    // ')' that returns every delimiter to top level (and is not inside a
    // string) closes the parameter list.
    if (text[i] == ')' && !tracker.in_string && tracker.AtTopLevel()) {
      return i;
    }
  }
  return std::string_view::npos;
}

std::string_view Preprocessor::ExtractBalancedArgs(std::string_view text) {
  auto open = text.find('(');
  if (open == std::string_view::npos) return {};
  int paren_depth = 0;
  bool in_string = false;
  for (size_t i = open; i < text.size(); ++i) {
    if (text[i] == '"' && (i == 0 || text[i - 1] != '\\')) {
      in_string = !in_string;
      continue;
    }
    if (in_string) continue;
    if (text[i] == '(')
      ++paren_depth;
    else if (text[i] == ')')
      --paren_depth;
    if (paren_depth == 0) return text.substr(open, i - open + 1);
  }
  return {};
}

std::vector<std::string_view> Preprocessor::SplitMacroArgs(
    std::string_view args_text) {
  std::vector<std::string_view> args;
  DelimiterTracker tracker;
  size_t start = 0;
  for (size_t i = 0; i < args_text.size(); ++i) {
    // §22.5.1: an escaped identifier (5.6.1) counts as a matched pair for the
    // purpose of argument splitting -- a comma or right parenthesis inside it
    // is part of the identifier, not a separator. An escaped identifier runs
    // from its leading backslash to the next white space, so skip the whole
    // token.
    if (!tracker.in_string && args_text[i] == '\\') {
      while (i < args_text.size() &&
             !std::isspace(static_cast<unsigned char>(args_text[i]))) {
        ++i;
      }
      --i;
      continue;
    }
    char prev = (i == 0) ? '\0' : args_text[i - 1];
    if (tracker.Update(args_text[i], prev)) continue;
    if (args_text[i] == ',' && tracker.AtTopLevel()) {
      args.push_back(Trim(args_text.substr(start, i - start)));
      start = i + 1;
    }
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
