#include <cctype>
#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

// The conditional compilation directives of §22.6 met within a line or within
// the text a macro's usage substitutes: FindInlineConditional locates an `ifdef
// or `ifndef with its matching `endif, and ExpandInlineConditionals replaces
// each such span with the branch its condition selects. The line-level readers
// in preprocessor.cpp and ExpandSubstitutedBody in preprocessor_inline.cpp run
// these before ExpandInlineMacros.

// Every caller hands text it has already seen open with a backtick.
static bool MatchesDirective(std::string_view text, std::string_view dir) {
  if (text.size() < 1 + dir.size()) return false;
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
  auto state = StringLiteralState::kOutside;
  for (size_t i = 0; i < line.size();
       i = StepOverStringSyntax(line, i, state)) {
    // A directive sequence sitting inside a string literal is hidden and must
    // not start an inline conditional expansion (22.6).
    if (!OutsideEveryString(state) || line[i] != '`') continue;
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

// The inline readers below run only on a conditional FindInlineConditional
// found an `endif for, so the text after the directive name holds that
// `endif's backtick, which is neither white space nor part of a name: a scan
// over either stops at it before the text runs out.
static size_t SkipWhitespace(const std::string& s, size_t pos) {
  while (std::isspace(static_cast<unsigned char>(s[pos]))) ++pos;
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
  has_expr = result[cond_start] == '(';
  if (has_expr) return ParseParenthesizedCondition(result, cond_start);
  size_t cond_end = cond_start;
  while (IsIdentChar(result[cond_end])) ++cond_end;
  return cond_end;
}

struct InlineCondBounds {
  // §22.6 (Syntax 22-5): where each `elsif group of the conditional opens, in
  // order, ahead of its `else.
  std::vector<size_t> elsif_pos;
  size_t else_pos;
  size_t endif_pos;
  // §22.6 (Syntax 22-5): whether a second `else stands in the conditional.
  bool second_else;
};

// Notes the directive opening `jr`, standing at `j`, in `bounds`, `depth`
// counting the conditionals open there; answers whether it is the `endif that
// closes the conditional being read.
static bool NoteInlineDirective(std::string_view jr, size_t j, int& depth,
                                InlineCondBounds& bounds) {
  if (MatchesDirective(jr, "ifdef") || MatchesDirective(jr, "ifndef")) {
    ++depth;
  } else if (MatchesDirective(jr, "endif")) {
    if (--depth == 0) bounds.endif_pos = j;
  } else if (depth == 1 && MatchesDirective(jr, "elsif")) {
    bounds.elsif_pos.push_back(j);
  } else if (depth == 1 && MatchesDirective(jr, "else")) {
    bounds.second_else =
        bounds.second_else || bounds.else_pos != std::string::npos;
    if (bounds.else_pos == std::string::npos) bounds.else_pos = j;
  }
  return depth == 0;
}

static InlineCondBounds FindElseAndEndif(const std::string& result,
                                         size_t search_start) {
  InlineCondBounds bounds{{}, std::string::npos, std::string::npos, false};
  int depth = 1;
  for (size_t j = search_start; j < result.size(); ++j) {
    if (result[j] != '`') continue;
    if (NoteInlineDirective(std::string_view(result).substr(j), j, depth,
                            bounds)) {
      break;
    }
  }
  return bounds;
}

// §22.6 (Syntax 22-5): the text of the group a conditional selects -- the
// first whose condition holds, the `ifdef's own (`cond_result`, its text from
// `cond_end`) and then each `elsif's in order, `eval` answering the truth of
// the condition an `elsif writes, and else the `else group, or nothing. Each
// group's text runs to the next group's directive.
static std::string SelectConditionalBlock(
    const std::string& result, bool cond_result, size_t cond_end,
    const InlineCondBounds& bounds,
    const std::function<bool(std::string_view, bool)>& eval) {
  std::vector<size_t> group_ends = bounds.elsif_pos;
  if (bounds.else_pos != std::string::npos)
    group_ends.push_back(bounds.else_pos);
  group_ends.push_back(bounds.endif_pos);
  if (cond_result) return result.substr(cond_end, group_ends[0] - cond_end);
  for (size_t k = 0; k < bounds.elsif_pos.size(); ++k) {
    size_t start = SkipWhitespace(result, bounds.elsif_pos[k] + 6);
    bool has_expr = false;
    size_t end = ParseInlineCondition(result, start, has_expr);
    if (eval(std::string_view(result).substr(start, end - start), has_expr))
      return result.substr(end, group_ends[k + 1] - end);
  }
  if (bounds.else_pos == std::string::npos) return {};
  return result.substr(bounds.else_pos + 5,
                       bounds.endif_pos - (bounds.else_pos + 5));
}

std::string Preprocessor::ExpandInlineConditionals(std::string_view line,
                                                   SourceLoc loc) {
  std::string result(line);
  auto eval = [this, loc](std::string_view condition, bool has_expr) {
    return has_expr ? EvalIfdefExpr(condition, loc)
                    : macros_.IsDefined(condition);
  };

  while (true) {
    size_t ifdef_pos = FindInlineConditional(result);
    if (ifdef_pos == std::string::npos) break;

    bool is_ifndef =
        MatchesDirective(std::string_view(result).substr(ifdef_pos), "ifndef");
    size_t cond_start =
        SkipWhitespace(result, ifdef_pos + std::string_view("`ifdef").size() +
                                   static_cast<size_t>(is_ifndef));

    bool has_expr = false;
    size_t cond_end = ParseInlineCondition(result, cond_start, has_expr);

    auto condition =
        std::string_view(result).substr(cond_start, cond_end - cond_start);
    // §22.6: a parenthesis the line never closes leaves no condition to read.
    if (has_expr && cond_end == result.size()) {
      diag_.Error(
          loc,
          "malformed ifdef_macro_expression '" + std::string(condition) + "'",
          Subclause("22.6"));
      break;
    }
    bool cond_result = eval(condition, has_expr) != is_ifndef;

    auto bounds = FindElseAndEndif(result, cond_end);
    if (bounds.endif_pos == std::string::npos) break;
    if (bounds.second_else) {
      diag_.Error(loc, "a second `else in one `ifdef or `ifndef",
                  Subclause("22.6"));
    }

    auto replacement =
        SelectConditionalBlock(result, cond_result, cond_end, bounds, eval);

    size_t span_end = bounds.endif_pos + 6;
    result.erase(ifdef_pos, span_end - ifdef_pos);
    result.insert(ifdef_pos, replacement);
  }

  return result;
}

// §5.9 inside a string of an ignored line: an escape takes the character after
// its backslash with it, a backslash ending the line continues the string onto
// the next one, and a quote closes it. Returns the index past what was read.
static size_t StepInsideIgnoredString(std::string_view text, size_t i,
                                      bool& open, bool& continued) {
  if (text[i] == '\\') {
    continued = i + 1 == text.size();
    return i + 2;
  }
  if (text[i] == '"') open = false;
  return i + 1;
}

// Outside a string: a backslash opens an escaped identifier (§5.6.1), which
// runs to white space and opens no string whatever it holds; a quote opens a
// string. A triple quote opens a string StripComments carries across lines
// itself, so nothing after it on the line is read; npos says so.
static size_t StepOutsideIgnoredString(std::string_view text, size_t i,
                                       bool& open) {
  if (text.substr(i, 3) == "\"\"\"") return std::string_view::npos;
  if (text[i] == '\\') {
    while (i < text.size() &&
           !std::isspace(static_cast<unsigned char>(text[i])))
      ++i;
    return i;
  }
  if (text[i] == '"') open = true;
  return i + 1;
}

// §22.6 (printed page 714): a block of text the compiler ignores still follows
// the lexical conventions of Clause 5, so the string literals of an ignored
// line are read as §5.9 has them read anywhere, and one left open at the end
// of the line with no backslash continuing it is reported.
void Preprocessor::NoteIgnoredLine(std::string_view line, SourceLoc loc) {
  bool line_opens_in_triple = in_triple_string_;
  std::string text = StripComments(line, in_block_comment_, in_triple_string_);
  if (line_opens_in_triple) return;
  bool open = in_ignored_string_;
  bool continued = false;
  size_t i = 0;
  while (i < text.size()) {
    continued = false;
    i = open ? StepInsideIgnoredString(text, i, open, continued)
             : StepOutsideIgnoredString(text, i, open);
  }
  in_ignored_string_ = open && continued;
  if (open && !continued) {
    diag_.Error(loc,
                "unterminated string literal in a block of text a conditional "
                "compilation directive ignores",
                Subclause("22.6"));
  }
}

}  // namespace delta
