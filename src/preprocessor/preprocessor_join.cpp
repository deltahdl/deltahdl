#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

static bool EndsWithBackslash(std::string_view line) {
  return !line.empty() && line.back() == '\\';
}

static bool HasOpenTripleQuote(std::string_view text) {
  int count = 0;
  for (size_t i = 0; i + 2 < text.size(); ++i) {
    if (text[i] == '"' && text[i + 1] == '"' && text[i + 2] == '"') {
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
    if (text[i] == '`' && text[i + 1] == '"' && text[i + 2] == '"' &&
        text[i + 3] == '"') {
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

// Returns the text up to an unquoted one-line comment (//), or the whole text
// if there is none.
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
    // §22.5.1: a one-line comment ends at the backslash continuation, so drop
    // the comment before joining — otherwise it would swallow the body that
    // continues on the next line.
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

    // §22.5.1: a backslash-newline in the macro text is replaced in the
    // expansion by a newline character (the backslash is dropped). The one
    // exception is a backslash-newline that falls inside a double-quoted string
    // literal, where both the backslash and the newline are omitted (see 5.9);
    // HasUnterminatedString(joined) reports that in-string state. A `""" span
    // keeps its embedded newlines the same way.
    if (HasOpenBacktickTripleQuote(joined) ||
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

// One physical line of a macro usage, comment-stripped as the loop strips a
// line it emits, so the parentheses counted are the ones in code and never
// one a comment holds. The marker of a blanked one-line comment goes as well:
// the join puts another line after this one, and a marker left standing would
// blank that line when the joined text is stripped again at emission.
static void AppendUsageLine(std::string_view line, bool& in_block_comment,
                            bool& in_triple_string, std::string& joined) {
  auto stripped = StripComments(line, in_block_comment, in_triple_string);
  joined += StripTrailingLineComment(stripped);
}

// Whether the line's first token is a directive other than a value one. A join
// must not read such a line as part of an argument list: a conditional or an
// `include standing there has to act, and would be lost into the arguments.
static bool LeadsWithDirective(std::string_view line) {
  auto trimmed = Preprocessor::Trim(line);
  if (trimmed.empty() || trimmed[0] != '`') return false;
  size_t end = 1;
  while (end < trimmed.size() && IsIdentChar(trimmed[end])) ++end;
  return IsDirectiveOtherThanValue(trimmed.substr(1, end - 1));
}

// Whether a line may carry on a usage whose name ended the line before it, with
// the list yet to open: its first token is the left parenthesis, or it holds
// nothing but white space and a one-line comment, which §5.3 and §5.4 make
// separators between the name and the parenthesis rather than tokens of their
// own.
static bool MayOpenList(std::string_view line) {
  auto probe = Preprocessor::Trim(StripTrailingLineComment(line));
  return probe.empty() || probe[0] == '(';
}

// §22.5.1 requires the actual arguments of a macro usage to be enclosed in
// parentheses and separated by commas, allows white space between the name and
// the left parenthesis, and places none of it on any particular line, so a list
// left open at the end of a physical line continues on the next one and a name
// ending a line has its list on a line after it. When the line at `cursor`
// leaves either unfinished, the lines after it are read in until the usage is
// complete, and the cursor is moved to the last of them. A space joins them
// rather than the newline that stood there: between two lines of one usage the
// newline is white space between tokens, and a space keeps the expansion on one
// output line, which the table NoteOutputLine fills counts on, recording one
// source line for each. Returns how many lines were added, which the loop adds
// to its line counter only after the usage is emitted: `__LINE__ (22.13) among
// the arguments and a report about the expansion both name the line the usage
// opened on. A list no later line closes is left as written, so that a mistyped
// usage does not read the rest of the file as its arguments: nothing is moved,
// and the loop processes the line alone as it did before this join existed. A
// list whose lines run through a directive is left the same way, since the
// directive has to act and could not from inside an argument, and so is a name
// alone whose next line opens no list, which the expander then rejects as a
// usage written without its parentheses.
//
// The strip state starts clear because an open block comment takes another
// path, and `end_of_macro_usage` answers kComplete without reading the text
// while a triple_quoted_string is open.
uint32_t JoinMacroUsage(
    LineCursor& cursor,
    const std::function<MacroUsageEnd(std::string_view)>& end_of_macro_usage,
    std::string& joined) {
  std::string_view src = cursor.src;
  std::string_view first_line = src.substr(cursor.pos, cursor.eol - cursor.pos);
  if (first_line.find('`') == std::string_view::npos) return 0;
  bool in_block_comment = false;
  bool in_triple_string = false;
  std::string acc;
  AppendUsageLine(first_line, in_block_comment, in_triple_string, acc);
  MacroUsageEnd end = end_of_macro_usage(acc);
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
    acc += ' ';
    AppendUsageLine(next_line, in_block_comment, in_triple_string, acc);
    end = end_of_macro_usage(acc);
    if (end == MacroUsageEnd::kComplete) {
      cursor.eol = eol;
      joined = std::move(acc);
      return lines_added;
    }
  }
  return 0;
}

}  // namespace delta
