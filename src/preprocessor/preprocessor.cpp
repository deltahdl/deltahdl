#include "preprocessor/preprocessor.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <sstream>

namespace delta {

Preprocessor::Preprocessor(SourceManager& src_mgr, DiagEngine& diag,
                           PreprocConfig config)
    : src_mgr_(src_mgr), diag_(diag), config_(std::move(config)) {
  for (const auto& [name, value] : config_.defines) {
    MacroDef def;
    def.name = name;
    def.body = value;
    macros_.Define(std::move(def));
  }

  DefinePredefined("SV_COV_START", "0");
  DefinePredefined("SV_COV_STOP", "1");
  DefinePredefined("SV_COV_RESET", "2");
  DefinePredefined("SV_COV_CHECK", "3");
  DefinePredefined("SV_COV_MODULE", "10");
  DefinePredefined("SV_COV_HIER", "11");
  DefinePredefined("SV_COV_ASSERTION", "20");
  DefinePredefined("SV_COV_FSM_STATE", "21");
  DefinePredefined("SV_COV_STATEMENT", "22");
  DefinePredefined("SV_COV_TOGGLE", "23");
  DefinePredefined("SV_COV_OVERFLOW", "-2");
  DefinePredefined("SV_COV_ERROR", "-1");
  DefinePredefined("SV_COV_NOCOV", "0");
  DefinePredefined("SV_COV_OK", "1");
  DefinePredefined("SV_COV_PARTIAL", "2");
}

void Preprocessor::DefinePredefined(std::string name, std::string body) {
  MacroDef def;
  def.name = std::move(name);
  def.body = std::move(body);
  macros_.Define(std::move(def));
}

std::string Preprocessor::Preprocess(uint32_t file_id) {
  auto content = src_mgr_.FileContent(file_id);
  return ProcessSource(content, file_id, 0);
}

std::string_view Preprocessor::Trim(std::string_view s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
    s.remove_prefix(1);
  }
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
    s.remove_suffix(1);
  }
  return s;
}

bool IsCompilerDirective(std::string_view name) {
  static constexpr std::string_view kDirectives[] = {
      "define",
      "undef",
      "undefineall",
      "ifdef",
      "ifndef",
      "elsif",
      "else",
      "endif",
      "include",
      "timescale",
      "resetall",
      "line",
      "pragma",
      "celldefine",
      "endcelldefine",
      "default_nettype",
      "unconnected_drive",
      "nounconnected_drive",
      "begin_keywords",
      "end_keywords",
      "default_decay_time",
      "default_trireg_strength",
      "delay_mode_distributed",
      "delay_mode_path",
      "delay_mode_unit",
      "delay_mode_zero",
  };
  for (auto d : kDirectives) {
    if (name == d) return true;
  }
  return false;
}

static bool SkipBacktickQuote(std::string_view body, size_t& i) {
  if (body[i] != '`') return false;
  if (i + 1 < body.size() && body[i + 1] == '"') {
    i += 1;
    return true;
  }
  if (i + 3 < body.size() && body[i + 1] == '\\' && body[i + 2] == '`' &&
      body[i + 3] == '"') {
    i += 3;
    return true;
  }
  return false;
}

static void ProcessQuoteChar(std::string_view body, size_t& i, bool& in_string,
                             bool& in_triple) {
  if (in_triple) {
    if (i + 2 < body.size() && body[i + 1] == '"' && body[i + 2] == '"') {
      in_triple = false;
      i += 2;
    }
    return;
  }
  if (in_string) {
    in_string = false;
    return;
  }
  if (i + 2 < body.size() && body[i + 1] == '"' && body[i + 2] == '"') {
    in_triple = true;
    i += 2;
    return;
  }
  in_string = true;
}

bool HasUnterminatedString(std::string_view body) {
  bool in_string = false;
  bool in_triple = false;
  for (size_t i = 0; i < body.size(); ++i) {
    if (SkipBacktickQuote(body, i)) continue;
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
      ProcessQuoteChar(body, i, in_string, in_triple);
    }
  }
  return in_string || in_triple;
}

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

// Per-line scan position over the source buffer driven by the preprocessing
// loop (22.x): `src` is the whole file text, `pos` the start offset of the
// current physical line, `eol` its end offset (advanced when a `define body is
// joined across continuation lines), and `line_num` the 1-based line counter.
struct LineCursor {
  std::string_view src;
  size_t pos;
  size_t& eol;
  uint32_t& line_num;
};

static std::string JoinDefineBody(LineCursor& cursor) {
  std::string_view src = cursor.src;
  size_t pos = cursor.pos;
  size_t& eol = cursor.eol;
  uint32_t& line_num = cursor.line_num;
  std::string_view first_line = src.substr(pos, eol - pos);
  std::string joined;
  AppendDefineLine(first_line, joined);

  while (eol < src.size() && DefineNeedsContinuation(first_line, joined)) {
    size_t next_start = eol + 1;
    size_t next_eol = src.find('\n', next_start);
    if (next_eol == std::string_view::npos) next_eol = src.size();
    std::string_view next_line = src.substr(next_start, next_eol - next_start);
    ++line_num;
    eol = next_eol;
    first_line = next_line;

    if (HasOpenBacktickTripleQuote(joined)) {
      joined += '\n';
    }
    AppendDefineLine(next_line, joined);
  }
  return joined;
}

static bool StartsWithDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  if (trimmed.size() < dir.size() + 1) {
    return false;
  }
  if (trimmed[0] != '`') {
    return false;
  }
  return trimmed.substr(1, dir.size()) == dir;
}

static std::string_view AfterDirective(std::string_view line,
                                       std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  auto rest = trimmed.substr(1 + dir.size());
  return Preprocessor::Trim(rest);
}

static std::pair<std::string_view, std::string_view> SplitFirstToken(
    std::string_view s) {
  size_t end = 0;
  while (end < s.size() && !std::isspace(static_cast<unsigned char>(s[end])))
    ++end;
  if (end >= s.size()) return {s, {}};
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

static std::pair<std::string_view, std::string_view> SplitTimescaleArg(
    std::string_view s) {
  auto slash = s.find('/');
  if (slash == std::string_view::npos) return {s, {}};
  auto after_slash = s.substr(slash + 1);
  auto prec = Preprocessor::Trim(after_slash);
  size_t end = 0;

  while (end < prec.size() &&
         std::isdigit(static_cast<unsigned char>(prec[end])))
    ++end;

  while (end < prec.size() &&
         std::isspace(static_cast<unsigned char>(prec[end])))
    ++end;

  while (end < prec.size() &&
         std::isalpha(static_cast<unsigned char>(prec[end])))
    ++end;
  auto ts_end = static_cast<size_t>(prec.data() + end - s.data());
  return {s.substr(0, ts_end), Preprocessor::Trim(s.substr(ts_end))};
}

static std::pair<std::string_view, std::string_view> SplitQuotedArg(
    std::string_view s) {
  auto first = s.find('"');
  if (first == std::string_view::npos) return {s, {}};
  auto second = s.find('"', first + 1);
  if (second == std::string_view::npos) return {s, {}};
  auto end = second + 1;
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

static bool StripBlockCommentContent(std::string_view line, size_t& i,
                                     std::string& result) {
  if (i + 1 < line.size() && line[i] == '*' && line[i + 1] == '/') {
    result += "*/";
    i += 2;
    return true;
  }
  result += ' ';
  ++i;
  return false;
}

static bool StripNormalChar(std::string_view line, size_t& i,
                            std::string& result, bool& in_block_comment) {
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '/') {
    result += "//";
    i += 2;
    while (i < line.size()) {
      result += ' ';
      ++i;
    }
    return true;
  }
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '*') {
    result += "/*";
    i += 2;
    in_block_comment = true;
    return false;
  }
  result += line[i++];
  return false;
}

static std::string StripComments(std::string_view line,
                                 bool& in_block_comment) {
  std::string result;
  result.reserve(line.size());
  bool in_string = false;
  size_t i = 0;

  while (i < line.size()) {
    if (in_block_comment) {
      if (StripBlockCommentContent(line, i, result)) in_block_comment = false;
      continue;
    }
    if (line[i] == '"' && (i == 0 || line[i - 1] != '\\')) {
      in_string = !in_string;
      result += line[i++];
      continue;
    }
    if (in_string) {
      result += line[i++];
      continue;
    }
    if (StripNormalChar(line, i, result, in_block_comment)) return result;
  }
  return result;
}

void Preprocessor::ExpandAndAppendLine(std::string_view line, uint32_t file_id,
                                       uint32_t line_num, std::string& output) {
  auto stripped = StripComments(line, in_block_comment_);
  auto conditioned = ExpandInlineConditionals(stripped);
  auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  output.append(expanded);
}

static size_t FindDirectiveInStripped(std::string_view stripped) {
  size_t i = 0;
  while (i < stripped.size()) {
    auto c = stripped[i];
    if (std::isspace(static_cast<unsigned char>(c))) {
      ++i;
      continue;
    }

    if (i + 1 < stripped.size() && c == '/' && stripped[i + 1] == '*') {
      auto close = stripped.find("*/", i + 2);
      if (close != std::string_view::npos) {
        i = close + 2;
        continue;
      }
      break;
    }
    if (i + 1 < stripped.size() && c == '/' && stripped[i + 1] == '/') {
      break;
    }
    return (c == '`') ? i : std::string_view::npos;
  }
  return std::string_view::npos;
}

// 22.2: a language element is allowed on the same line before a directive.
// FindDirectiveInStripped only reports a directive that begins the line; this
// locates a directive that follows code, so the preceding element is emitted
// and the directive still acts. Backticks inside string literals are not
// directives, and a backtick that introduces a name absent from the directive
// set is a macro usage rather than a directive, so both are skipped.
static bool BacktickIntroducesDirective(std::string_view s, size_t i) {
  size_t start = i + 1;
  size_t end = start;
  while (end < s.size() && IsIdentChar(s[end])) ++end;
  return end > start && IsCompilerDirective(s.substr(start, end - start));
}

static size_t FindMidLineDirective(std::string_view s) {
  bool in_string = false;
  for (size_t i = 0; i < s.size(); ++i) {
    char c = s[i];
    if (c == '"' && (i == 0 || s[i - 1] != '\\') &&
        (i == 0 || s[i - 1] != '`')) {
      in_string = !in_string;
      continue;
    }
    if (in_string) continue;
    if (c == '`' && BacktickIntroducesDirective(s, i)) {
      return i;
    }
  }
  return std::string_view::npos;
}

bool Preprocessor::ProcessBlockCommentLine(std::string_view line,
                                           uint32_t file_id, uint32_t line_num,
                                           int depth, std::string& output) {
  auto close = line.find("*/");
  if (close == std::string_view::npos) {
    output.append(line);
    output.push_back('\n');
    return true;
  }
  output.append(line.substr(0, close + 2));
  in_block_comment_ = false;
  auto remainder = line.substr(close + 2);
  if (!Trim(remainder).empty()) {
    bool handled =
        ProcessDirective(remainder, file_id, line_num, depth, output);
    if (!handled && IsActive()) {
      ExpandAndAppendLine(remainder, file_id, line_num, output);
    }
  }
  output.push_back('\n');
  return true;
}

void Preprocessor::SkipBlockCommentLine(std::string_view line, uint32_t file_id,
                                        uint32_t line_num, int depth,
                                        std::string& output) {
  auto close = line.find("*/");
  if (close != std::string_view::npos) {
    in_block_comment_ = false;
    auto remainder = line.substr(close + 2);
    if (!Trim(remainder).empty()) {
      // Text after the comment close may be a directive (e.g. `endif) that
      // must still act on the conditional stack while the block is skipped.
      if (!ProcessDirective(remainder, file_id, line_num, depth, output) &&
          !IsActive()) {
        StripComments(remainder, in_block_comment_);
      }
    }
  }
  output.push_back('\n');
}

static bool DefineSpansMultipleLines(std::string_view line) {
  if (!StartsWithDirective(line, "define")) return false;
  auto body_start = AfterDirective(line, "define");
  return EndsWithBackslash(line) || HasOpenTripleQuote(body_start) ||
         HasOpenBlockComment(body_start);
}

// How a comment-stripped active line (22.2) should be split: either it opens
// with a directive, contains a directive after a language element, or is wholly
// ordinary text. The directive part begins at split_pos; any leading text spans
// [0, split_pos).
struct ActiveLineSplit {
  enum class Kind : std::uint8_t {
    kLeadingDirective,
    kMidLineDirective,
    kPlainText
  } kind;
  size_t split_pos;
};

static ActiveLineSplit ClassifyActiveLine(std::string_view stripped) {
  size_t dir_pos = FindDirectiveInStripped(stripped);
  if (dir_pos != std::string_view::npos)
    return {ActiveLineSplit::Kind::kLeadingDirective, dir_pos};
  size_t mid = FindMidLineDirective(stripped);
  if (mid != std::string_view::npos)
    return {ActiveLineSplit::Kind::kMidLineDirective, mid};
  return {ActiveLineSplit::Kind::kPlainText, 0};
}

// Callbacks for emitting one comment-stripped, conditional-stack-active line
// (22.2). expand_and_emit fully expands ordinary text; emit_directive_or_text
// runs a fragment as a directive or, failing that, expands it as text. They are
// supplied by ProcessSource because the underlying work touches private state.
struct ActiveLineEmit {
  std::function<void(std::string_view)> expand_and_emit;
  std::function<void(std::string_view)> emit_directive_or_text;
};

// Emit an already comment-stripped active line, routing it per its split kind.
static void EmitActiveLine(std::string_view view, const ActiveLineEmit& emit,
                           std::string& output) {
  ActiveLineSplit split = ClassifyActiveLine(view);
  switch (split.kind) {
    case ActiveLineSplit::Kind::kLeadingDirective:
      if (split.split_pos > 0) output.append(view.substr(0, split.split_pos));
      emit.emit_directive_or_text(view.substr(split.split_pos));
      return;
    case ActiveLineSplit::Kind::kMidLineDirective:
      emit.expand_and_emit(view.substr(0, split.split_pos));
      emit.emit_directive_or_text(view.substr(split.split_pos));
      return;
    case ActiveLineSplit::Kind::kPlainText:
      emit.expand_and_emit(view);
      return;
  }
}

// Callbacks the line loop uses to act on each physical source line. Each wraps
// private Preprocessor work so the loop itself can live as a free function.
struct PreprocLoopOps {
  std::function<bool()> in_block_comment;
  std::function<void(std::string_view)> continue_block_comment;
  std::function<bool(std::string_view)> run_directive;
  std::function<bool()> is_active;
  std::function<void(std::string_view)> emit_active_line;
  std::function<void(std::string_view)> note_ignored_line;
};

// Process one ordinary (non-block-comment) source line: a `define whose body
// spans multiple physical lines is first joined, then the line is run as a
// directive, emitted as active text, or (inside an ignored block) only scanned
// so an opening block comment is tracked across lines (22.6).
static void ProcessOrdinaryLine(std::string_view line, LineCursor& cursor,
                                const PreprocLoopOps& ops) {
  std::string joined;
  if (DefineSpansMultipleLines(line)) {
    joined = JoinDefineBody(cursor);
    line = joined;
  }
  if (ops.run_directive(line)) return;
  if (ops.is_active())
    ops.emit_active_line(line);
  else
    ops.note_ignored_line(line);
}

// Drive the per-line preprocessing loop (22.x). An open block comment continues
// with its own newline handling; every other line is processed and followed by
// a single newline. Emitted text is appended to output.
static void RunPreprocLoop(std::string_view src, uint32_t& line_num,
                           const PreprocLoopOps& ops, std::string& output) {
  size_t pos = 0;
  while (pos < src.size()) {
    size_t eol = src.find('\n', pos);
    if (eol == std::string_view::npos) eol = src.size();
    std::string_view line = src.substr(pos, eol - pos);
    ++line_num;
    if (ops.in_block_comment()) {
      ops.continue_block_comment(line);
    } else {
      LineCursor cursor{src, pos, eol, line_num};
      ProcessOrdinaryLine(line, cursor, ops);
      output.push_back('\n');
    }
    pos = eol + 1;
  }
}

std::string Preprocessor::ProcessSource(std::string_view src, uint32_t file_id,
                                        int depth) {
  if (depth > kMaxIncludeDepth) {
    diag_.Error({file_id, 1, 1}, "include depth exceeds maximum of 15");
    return "";
  }

  uint32_t line_num = 0;
  std::string output;
  output.reserve(src.size());

  // Conditionally expand a fragment (22.5.1 inline conditionals + macros),
  // track any design element it introduces, then emit it.
  ActiveLineEmit emit;
  emit.expand_and_emit = [&](std::string_view fragment) {
    auto conditioned = ExpandInlineConditionals(std::string(fragment));
    auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
    TrackDesignElement(Trim(expanded));
    output.append(expanded);
  };
  // Run a fragment through ProcessDirective; if it was not a directive, emit it
  // as ordinary text with full expansion.
  emit.emit_directive_or_text = [&](std::string_view fragment) {
    if (!ProcessDirective(fragment, file_id, line_num, depth, output))
      emit.expand_and_emit(fragment);
  };

  PreprocLoopOps ops;
  ops.in_block_comment = [&] { return in_block_comment_; };
  ops.is_active = [&] { return IsActive(); };
  // An open block comment (22.6) emits or skips its text and handles its own
  // trailing newline; a directive may still follow the comment close.
  ops.continue_block_comment = [&](std::string_view line) {
    if (IsActive())
      ProcessBlockCommentLine(line, file_id, line_num, depth, output);
    else
      SkipBlockCommentLine(line, file_id, line_num, depth, output);
  };
  ops.run_directive = [&](std::string_view line) {
    return ProcessDirective(line, file_id, line_num, depth, output);
  };
  ops.emit_active_line = [&](std::string_view line) {
    auto stripped = StripComments(std::string(line), in_block_comment_);
    // An inline `ifdef…`endif resolved on this line (22.6) must go through the
    // inline conditional expander; the mid-line directive dispatch would
    // instead push it onto the multi-line conditional stack and drop the
    // trailing text.
    if (HasInlineConditional(stripped)) {
      emit.expand_and_emit(stripped);
      return;
    }
    EmitActiveLine(stripped, emit, output);
  };
  // Inside an ignored block nothing is emitted, but track an opening block
  // comment so a later in-comment directive stays hidden (22.6).
  ops.note_ignored_line = [&](std::string_view line) {
    StripComments(line, in_block_comment_);
  };

  RunPreprocLoop(src, line_num, ops, output);
  return output;
}

void Preprocessor::OutputText(std::string_view text, uint32_t file_id,
                              uint32_t line_num, std::string& output) {
  if (Trim(text).empty()) return;
  auto stripped = StripComments(text, in_block_comment_);
  auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  output.append(expanded);
}

void Preprocessor::OutputPreExpanded(std::string_view text,
                                     std::string& output) {
  if (Trim(text).empty()) return;
  auto stripped = StripComments(text, in_block_comment_);
  TrackDesignElement(Trim(std::string_view(stripped)));
  output.append(stripped);
}

void Preprocessor::OutputRemainder(std::string_view line,
                                   std::string_view directive, uint32_t file_id,
                                   uint32_t line_num, std::string& output) {
  OutputText(AfterDirective(line, directive), file_id, line_num, output);
}

void Preprocessor::ProcessDirectiveRemainder(std::string_view line,
                                             std::string_view directive,
                                             SourceLoc loc, int depth,
                                             std::string& output) {
  auto rest = AfterDirective(line, directive);
  auto trimmed = Trim(rest);
  if (!trimmed.empty() && trimmed.front() == '`' &&
      ProcessDirective(rest, loc.file_id, loc.line, depth, output)) {
    return;
  }
  OutputText(rest, loc.file_id, loc.line, output);
}

bool Preprocessor::RejectInsideDesignElement(std::string_view directive_name,
                                             SourceLoc loc) {
  if (design_element_depth_ == 0) return false;
  std::string msg = "`";
  msg.append(directive_name);
  msg.append(" illegal inside a design element");
  diag_.Error(loc, msg);
  return true;
}

void Preprocessor::ResetDirectiveState() {
  default_net_type_ = NetType::kWire;
  in_celldefine_ = false;
  unconnected_drive_ = NetType::kWire;
  has_timescale_ = false;
  current_timescale_ = TimeScale{};
  default_decay_time_ = 0;
  default_decay_time_real_ = 0.0;
  default_decay_time_infinite_ = true;
  default_trireg_strength_ = 0;
  has_default_trireg_strength_ = false;
  delay_mode_directive_ = DelayModeDirective::kNone;
}

bool Preprocessor::ProcessDelayModeDirective(std::string_view line,
                                             SourceLoc loc) {
  if (StartsWithDirective(line, "delay_mode_distributed")) {
    if (RejectInsideDesignElement("delay_mode_distributed", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kDistributed;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_path")) {
    if (RejectInsideDesignElement("delay_mode_path", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kPath;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_unit")) {
    if (RejectInsideDesignElement("delay_mode_unit", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kUnit;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_zero")) {
    if (RejectInsideDesignElement("delay_mode_zero", loc)) return true;
    delay_mode_directive_ = DelayModeDirective::kZero;
    return true;
  }
  return false;
}

bool Preprocessor::ProcessSimpleStateDirective(std::string_view line,
                                               SourceLoc loc, int depth,
                                               std::string& output) {
  if (StartsWithDirective(line, "endcelldefine")) {
    in_celldefine_ = false;
    ProcessDirectiveRemainder(line, "endcelldefine", loc, depth, output);
    return true;
  }
  if (StartsWithDirective(line, "celldefine")) {
    in_celldefine_ = true;
    ProcessDirectiveRemainder(line, "celldefine", loc, depth, output);
    return true;
  }
  if (StartsWithDirective(line, "pragma")) {
    auto rest = Trim(AfterDirective(line, "pragma"));
    if (rest.empty()) {
      diag_.Error(loc, "`pragma requires a pragma_name");
    } else {
      char first = rest.front();
      if (!std::isalpha(static_cast<unsigned char>(first)) && first != '_') {
        diag_.Error(loc, "`pragma pragma_name must be a simple identifier");
      }
    }
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessExpandedStateDirective(std::string_view line,
                                                 SourceLoc loc,
                                                 uint32_t file_id,
                                                 uint32_t line_num,
                                                 std::string& output) {
  if (StartsWithDirective(line, "timescale")) {
    if (RejectInsideDesignElement("timescale", loc)) return true;
    auto rest = AfterDirective(line, "timescale");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [ts_arg, remainder] = SplitTimescaleArg(expanded);
    HandleTimescale(ts_arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "default_nettype")) {
    if (RejectInsideDesignElement("default_nettype", loc)) return true;
    auto rest = AfterDirective(line, "default_nettype");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleDefaultNettype(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "unconnected_drive")) {
    if (RejectInsideDesignElement("unconnected_drive", loc)) return true;
    auto rest = AfterDirective(line, "unconnected_drive");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleUnconnectedDrive(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "nounconnected_drive")) {
    if (RejectInsideDesignElement("nounconnected_drive", loc)) return true;
    unconnected_drive_ = NetType::kWire;
    OutputRemainder(line, "nounconnected_drive", file_id, line_num, output);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessMiscStateDirective(std::string_view line,
                                             SourceLoc loc, uint32_t file_id,
                                             uint32_t line_num,
                                             std::string& output) {
  if (StartsWithDirective(line, "resetall")) {
    if (RejectInsideDesignElement("resetall", loc)) return true;
    ResetDirectiveState();
    OutputRemainder(line, "resetall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "default_decay_time")) {
    if (RejectInsideDesignElement("default_decay_time", loc)) return true;
    HandleDefaultDecayTime(AfterDirective(line, "default_decay_time"), loc);
    return true;
  }
  if (StartsWithDirective(line, "default_trireg_strength")) {
    if (RejectInsideDesignElement("default_trireg_strength", loc)) return true;
    HandleDefaultTriregStrength(AfterDirective(line, "default_trireg_strength"),
                                loc);
    return true;
  }
  return ProcessDelayModeDirective(line, loc);
}

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc,
                                         int depth, std::string& output) {
  // loc already carries file_id/line, so they are not separate parameters here
  // (keeping the arity <= 5 for readability-function-size).
  if (ProcessSimpleStateDirective(line, loc, depth, output)) return true;
  if (ProcessExpandedStateDirective(line, loc, loc.file_id, loc.line, output))
    return true;
  return ProcessMiscStateDirective(line, loc, loc.file_id, loc.line, output);
}

static size_t FindUndefNameEnd(std::string_view text) {
  size_t name_end = 0;
  if (!text.empty() && text[0] == '\\') {
    name_end = 1;
    while (name_end < text.size() &&
           !std::isspace(static_cast<unsigned char>(text[name_end])))
      ++name_end;
  } else {
    while (name_end < text.size() && IsIdentChar(text[name_end])) ++name_end;
  }
  return name_end;
}

void Preprocessor::ProcessIncludeDirective(std::string_view line, SourceLoc loc,
                                           int depth, std::string& output) {
  auto inc_arg = AfterDirective(line, "include");
  auto expanded_arg = ExpandInlineMacros(inc_arg, loc.file_id, loc.line);
  auto trimmed_arg = Trim(std::string_view(expanded_arg));
  bool angle_bracket = !trimmed_arg.empty() && trimmed_arg.front() == '<';
  HandleInclude(expanded_arg, loc, depth, output, angle_bracket);
}

bool Preprocessor::ProcessKeywordsDirective(std::string_view line,
                                            SourceLoc loc, uint32_t file_id,
                                            uint32_t line_num,
                                            std::string& output) {
  if (StartsWithDirective(line, "begin_keywords")) {
    if (RejectInsideDesignElement("begin_keywords", loc)) return true;
    auto rest = AfterDirective(line, "begin_keywords");
    auto [bk_arg, remainder] = SplitQuotedArg(rest);
    HandleBeginKeywords(bk_arg, loc, output);
    OutputText(remainder, file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "end_keywords")) {
    if (RejectInsideDesignElement("end_keywords", loc)) return true;
    HandleEndKeywords(loc, output);
    OutputRemainder(line, "end_keywords", file_id, line_num, output);
    return true;
  }
  return false;
}

bool Preprocessor::ProcessActiveOnlyDirective(std::string_view line,
                                              SourceLoc loc, int depth,
                                              std::string& output) {
  uint32_t file_id = loc.file_id;
  uint32_t line_num = loc.line;
  if (StartsWithDirective(line, "include")) {
    ProcessIncludeDirective(line, loc, depth, output);
    return true;
  }
  if (ProcessKeywordsDirective(line, loc, file_id, line_num, output))
    return true;
  if (ProcessStateDirective(line, loc, depth, output)) return true;
  auto trimmed = Trim(line);
  return TryExpandMacro(trimmed, output, file_id, line_num, depth);
}

bool Preprocessor::ProcessDirective(std::string_view line, uint32_t file_id,
                                    uint32_t line_num, int depth,
                                    std::string& output) {
  auto trimmed = Trim(line);
  if (trimmed.empty() || trimmed[0] != '`') return false;
  SourceLoc loc = {file_id, line_num, 1};

  if (StartsWithDirective(line, "define")) {
    HandleDefine(AfterDirective(line, "define"), loc);
    return true;
  }
  if (StartsWithDirective(line, "undefineall")) {
    macros_.UndefineAll();
    OutputRemainder(line, "undefineall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "undef")) {
    auto trimmed_rest = Trim(AfterDirective(line, "undef"));
    size_t name_end = FindUndefNameEnd(trimmed_rest);
    HandleUndef(trimmed_rest.substr(0, name_end), loc);
    if (IsActive()) {
      OutputText(Trim(trimmed_rest.substr(name_end)), file_id, line_num,
                 output);
    }
    return true;
  }
  if (ProcessConditionalDirective(line, file_id, line_num, output)) return true;
  if (IsActive() && ProcessActiveOnlyDirective(line, loc, depth, output))
    return true;
  return false;
}

bool Preprocessor::ProcessConditionalDirective(std::string_view line,
                                               uint32_t file_id,
                                               uint32_t line_num,
                                               std::string& output) {
  if (StartsWithDirective(line, "ifdef")) {
    HandleIfdef(AfterDirective(line, "ifdef"), false);
    return true;
  }
  if (StartsWithDirective(line, "ifndef")) {
    HandleIfdef(AfterDirective(line, "ifndef"), true);
    return true;
  }
  if (StartsWithDirective(line, "elsif")) {
    HandleElsif(AfterDirective(line, "elsif"));
    return true;
  }
  if (StartsWithDirective(line, "else")) {
    HandleElse();

    if (IsActive()) OutputRemainder(line, "else", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "endif")) {
    HandleEndif();

    if (IsActive()) OutputRemainder(line, "endif", file_id, line_num, output);
    return true;
  }
  return false;
}

}  // namespace delta
