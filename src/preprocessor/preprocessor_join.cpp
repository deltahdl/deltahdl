#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

static bool EndsWithBackslash(std::string_view line) {
  return !line.empty() && line.back() == '\\';
}

static bool HasOpenTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 2 < text.size(); ++i) {
    if (text.substr(i).starts_with("\"\"\"")) {
      if (i > 0 && text[i - 1] == '`') {
        i += 2;
        continue;
      }
      ++count;
      i += 2;
    }
  }
  return count % 2 != 0;
}

static bool HasOpenBacktickTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 3 < text.size(); ++i) {
    if (text.substr(i).starts_with("`\"\"\"")) {
      ++count;
      i += 3;
    }
  }
  return count % 2 != 0;
}

static bool IsUnescapedQuote(std::string_view text, size_t i) {
  return text[i] == '"' && (i == 0 || text[i - 1] != '\\') &&
         (i == 0 || text[i - 1] != '`');
}

static bool TryToggleBlockComment(std::string_view text, size_t& i,
                                  bool& in_block) {
  if (i + 1 >= text.size()) return false;
  if (!in_block && text[i] == '/' && text[i + 1] == '*') {
    in_block = true;
    ++i;
    return true;
  }
  if (in_block && text[i] == '*' && text[i + 1] == '/') {
    in_block = false;
    ++i;
    return true;
  }
  return false;
}

static bool HasOpenBlockComment(std::string_view text) {
  bool in_string = false;
  bool in_block = false;
  for (size_t i = 0; i < text.size(); ++i) {
    if (IsUnescapedQuote(text, i)) {
      if (!in_block) in_string = !in_string;
      continue;
    }
    if (in_string) continue;
    if (!in_block && text.substr(i).starts_with("//")) return false;
    TryToggleBlockComment(text, i, in_block);
  }
  return in_block;
}

static bool DefineNeedsContinuation(std::string_view line_text,
                                    const std::string& accumulated) {
  if (EndsWithBackslash(line_text)) return true;
  if (HasOpenTripleQuote(accumulated)) return true;
  if (HasOpenBlockComment(accumulated)) return true;
  return false;
}

static std::string_view StripTrailingLineComment(std::string_view text) {
  bool in_string = false;
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (c == '"' && (i == 0 || text[i - 1] != '\\')) {
      in_string = !in_string;
    } else if (!in_string && c == '/' && i + 1 < text.size() &&
               text[i + 1] == '/') {
      return text.substr(0, i);
    }
  }
  return text;
}

static void AppendDefineLine(std::string_view line, std::string& joined) {
  if (EndsWithBackslash(line)) {
    joined.append(StripTrailingLineComment(line.substr(0, line.size() - 1)));
  } else {
    joined.append(line);
  }
}

std::string JoinDefineBody(LineCursor& cursor) {
  std::string_view src = cursor.src;
  size_t pos = cursor.pos;
  size_t& eol = cursor.eol;
  uint32_t& line_num = cursor.line_num;
  std::string_view first_line = src.substr(pos, eol - pos);
  std::string joined;
  AppendDefineLine(first_line, joined);

  while (eol < src.size() && DefineNeedsContinuation(first_line, joined)) {
    bool backslash_join = EndsWithBackslash(first_line);
    size_t next_start = eol + 1;
    size_t next_eol = src.find('\n', next_start);
    if (next_eol == std::string_view::npos) next_eol = src.size();
    std::string_view next_line = src.substr(next_start, next_eol - next_start);
    ++line_num;
    eol = next_eol;
    first_line = next_line;

    if (HasOpenBacktickTripleQuote(joined) || HasOpenTripleQuote(joined) ||
        (backslash_join && !HasUnterminatedString(joined))) {
      joined += '\n';
    }
    AppendDefineLine(next_line, joined);
  }
  return joined;
}

bool DefineSpansMultipleLines(std::string_view line) {
  if (!StartsWithDirective(line, "define")) return false;
  auto body_start = AfterDirective(line, "define");
  return EndsWithBackslash(line) || HasOpenTripleQuote(body_start) ||
         HasOpenBlockComment(body_start);
}

namespace {
struct UsageJoin {
  bool in_block_comment = false;
  bool in_triple_string = false;
  std::string text;
  std::vector<std::string> comments;
  std::string line_comments;
};
}  // namespace

static size_t StartOfEndingComment(const std::string& marked) {
  return marked.rfind(kCommentMark, marked.size() - 2) - 2;
}

static void AppendUsageLine(std::string_view line, UsageJoin& join) {
  auto marked = StripComments(line, join.in_block_comment,
                              join.in_triple_string, &join.comments);
  if (join.in_block_comment || marked.empty() ||
      marked.back() != kCommentMark) {
    join.text += marked;
    return;
  }
  size_t comment = StartOfEndingComment(marked);
  join.text.append(marked, 0, comment);
  join.line_comments += '\n';
  join.line_comments.append(marked, comment);
}

static void PlaceLineComments(UsageJoin& join) {
  if (!join.in_block_comment) {
    join.text += join.line_comments;
  } else if (!join.line_comments.empty()) {
    join.text.insert(StartOfEndingComment(join.text),
                     join.line_comments + '\n');
  }
}

static bool LeadsWithDirective(std::string_view line) {
  auto trimmed = Preprocessor::Trim(line);
  if (trimmed.empty() || trimmed[0] != '`') return false;
  size_t end = 1;
  while (end < trimmed.size() && IsIdentChar(trimmed[end])) ++end;
  return IsDirectiveOtherThanValue(trimmed.substr(1, end - 1));
}

static bool MayOpenList(std::string_view line) {
  auto probe = Preprocessor::Trim(StripTrailingLineComment(line));
  return probe.empty() || probe[0] == '(';
}

uint32_t JoinMacroUsage(
    LineCursor& cursor,
    const std::function<MacroUsageEnd(std::string_view)>& end_of_macro_usage,
    std::string& joined) {
  std::string_view src = cursor.src;
  std::string_view first_line = src.substr(cursor.pos, cursor.eol - cursor.pos);
  if (first_line.find('`') == std::string_view::npos) return 0;
  UsageJoin join;
  AppendUsageLine(first_line, join);
  MacroUsageEnd end = end_of_macro_usage(join.text);
  if (end == MacroUsageEnd::kComplete) return 0;

  size_t eol = cursor.eol;
  uint32_t lines_added = 0;
  while (eol < src.size()) {
    size_t next_start = eol + 1;
    eol = src.find('\n', next_start);
    if (eol == std::string_view::npos) eol = src.size();
    std::string_view next_line = src.substr(next_start, eol - next_start);
    if (LeadsWithDirective(next_line)) return 0;
    if (end == MacroUsageEnd::kNameAlone && !MayOpenList(next_line)) return 0;
    ++lines_added;
    join.text += ' ';
    AppendUsageLine(next_line, join);
    end = end_of_macro_usage(join.text);
    if (end == MacroUsageEnd::kComplete) {
      cursor.eol = eol;
      PlaceLineComments(join);
      RestoreComments(join.text, 0, join.comments);
      joined = std::move(join.text);
      return lines_added;
    }
  }
  return 0;
}

bool EndsInContinuedQuotedString(std::string_view text) {
  bool in_string = false;
  size_t i = 0;
  while (i < text.size()) {
    if (text[i] == '\\') {
      i = in_string ? i + 2 : EndOfEscapedIdentifier(text, i);
      continue;
    }
    if (text[i] == '"') in_string = !in_string;
    ++i;
  }
  return in_string && i > text.size();
}

bool CopyContinuedQuotedString(std::string_view& line, std::string& output,
                               bool& continued) {
  if (!continued) return false;
  size_t i = 0;
  while (i < line.size() && line[i] != '"') i += line[i] == '\\' ? 2 : 1;
  continued = i > line.size();
  const size_t kEnd = std::min(i + 1, line.size());
  output.append(line.substr(0, kEnd));
  line.remove_prefix(kEnd);
  return true;
}

}  // namespace delta
