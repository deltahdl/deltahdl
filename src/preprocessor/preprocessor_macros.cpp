#include <algorithm>
#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/macro_table.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

bool IsIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$';
}

static void SkipSpaces(std::string_view& s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s[0]))) {
    s.remove_prefix(1);
  }
}

static std::string_view ParenthesizedSpan(std::string_view name) {
  int depth = 0;
  for (size_t i = 0; i < name.size(); ++i) {
    if (name[i] == '(') ++depth;
    if (name[i] == ')' && --depth == 0) return name.substr(0, i + 1);
  }
  return name;
}

bool Preprocessor::EvalIfdefCondition(std::string_view name,
                                      std::string_view directive,
                                      SourceLoc loc) {
  if (name.empty()) {
    diag_.Error(loc, "`" + std::string(directive) + " is missing its condition",
                Subclause("22.6"));
    return false;
  }
  if (name[0] == '(') return EvalIfdefExpr(ParenthesizedSpan(name), loc);
  size_t len = name[0] == '\\'
                   ? std::min(name.find_first_of(" \t\f\r\n"), name.size())
                   : 0;
  while (len < name.size() && IsIdentChar(name[len])) ++len;
  if (len == 0) {
    diag_.Error(loc,
                "'" + std::string(name) + "' after `" + std::string(directive) +
                    " is no ifdef_condition",
                Subclause("22.6"));
    return false;
  }
  return macros_.IsDefined(name.substr(0, len));
}

bool Preprocessor::EvalIfdefExpr(std::string_view expr, SourceLoc loc) {
  auto e = Trim(expr);
  ifdef_expr_malformed_ = false;
  bool result = EvalIfdefEquiv(e);
  SkipSpaces(e);
  if (ifdef_expr_malformed_ || !e.empty()) {
    diag_.Error(
        loc,
        "malformed ifdef_macro_expression '" + std::string(Trim(expr)) + "'",
        Subclause("22.6"));
  }
  return result;
}

bool Preprocessor::EvalIfdefEquiv(std::string_view& expr) {
  bool lhs = EvalIfdefOr(expr);
  SkipSpaces(expr);
  if (expr.starts_with("<->")) {
    expr.remove_prefix(3);
    return lhs == EvalIfdefEquiv(expr);
  }
  if (expr.starts_with("->")) {
    expr.remove_prefix(2);
    bool rhs = EvalIfdefEquiv(expr);
    return !lhs || rhs;
  }
  return lhs;
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
    if (!expr.starts_with(')')) {
      ifdef_expr_malformed_ = true;
      return result;
    }
    expr.remove_prefix(1);
    return result;
  }

  size_t len = 0;
  while (len < expr.size() && IsIdentChar(expr[len])) ++len;
  if (len == 0) ifdef_expr_malformed_ = true;
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
    if (arg.empty() && macro.param_defaults[i] != "\x01") {
      resolved.emplace_back(macro.param_defaults[i]);
    } else {
      resolved.emplace_back(ExpandInlineMacros(arg, loc.file_id, loc.line));
    }
  }
  std::vector<std::string_view> resolved_views;
  resolved_views.reserve(resolved.size());
  for (const auto& s : resolved) resolved_views.emplace_back(s);
  return SubstituteParams(macro.body, macro.params, resolved_views);
}

size_t EndOfEscapedIdentifier(std::string_view text, size_t i) {
  while (i < text.size() &&
         !std::isspace(static_cast<unsigned char>(text[i]))) {
    ++i;
  }
  return i;
}

struct DelimiterTracker {
  int paren_depth = 0;
  int bracket_depth = 0;
  int brace_depth = 0;
  bool in_string = false;
  bool in_triple = false;

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

static void AppendMacroParam(std::string_view token,
                             std::vector<std::string>& params,
                             std::vector<std::string>& defaults) {
  auto trimmed = Preprocessor::Trim(token);
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
    if (!inside && text[i] == ')' && tracker.AtTopLevel()) return i;
    i = next;
  }
  return std::string_view::npos;
}

std::string_view Preprocessor::ExtractBalancedArgs(std::string_view text) {
  auto open = text.find('(');
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
  for (size_t p = 0; p < params.size(); ++p) {
    if (token == params[p]) {
      result.append(args[p]);
      return;
    }
  }
  result.append(token);
}

static size_t AppendMacroQuote(std::string_view body, size_t i,
                               std::string& result) {
  std::string_view at = body.substr(i);
  if (at.starts_with("`\\`\"")) {
    result += "\\\"";
    return 4;
  }
  if (at.starts_with("`\"")) {
    result += '"';
    return 2;
  }
  if (at.starts_with("``")) return 2;
  return 0;
}

static size_t CopyStringChar(std::string_view body, size_t i, bool& in_string,
                             std::string& result) {
  if (body[i] == '\\') {
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
