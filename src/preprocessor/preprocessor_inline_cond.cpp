#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/preprocessor.h"

namespace delta {

// The conditional compilation directives of §22.6 met within a line or within
// the text a macro's usage substitutes: FindInlineConditional locates an `ifdef
// or `ifndef with its matching `endif, and ExpandInlineConditionals replaces
// each such span with the branch its condition selects. The line-level readers
// in preprocessor.cpp and ExpandSubstitutedBody in preprocessor_inline.cpp run
// these before ExpandInlineMacros.

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

}  // namespace delta
