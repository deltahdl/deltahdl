#include <cctype>

#include "preprocessor/preprocessor.h"

namespace delta {

bool IsIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$';
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

// --- Macro expansion helpers ---

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
        macro.param_defaults[i] != "\x01") {
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
      // Sentinel: \x01 means "no default specified" vs "" = explicit empty.
      defaults.emplace_back("\x01");
    }
    pos = comma + 1;
  }
  return params;
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

// Track balanced delimiters: parentheses, brackets, braces, and strings.
struct DelimiterTracker {
  int paren_depth = 0;
  int bracket_depth = 0;
  int brace_depth = 0;
  bool in_string = false;

  // Update state for a character. Returns true if inside a nested context.
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

// §22.5.1: Split macro arguments respecting balanced (), [], {}, and "".
std::vector<std::string_view> Preprocessor::SplitMacroArgs(
    std::string_view args_text) {
  std::vector<std::string_view> args;
  DelimiterTracker tracker;
  size_t start = 0;
  for (size_t i = 0; i < args_text.size(); ++i) {
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

}  // namespace delta
