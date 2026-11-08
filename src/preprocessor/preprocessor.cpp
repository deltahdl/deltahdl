#include "preprocessor/preprocessor.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "preprocessor/macro_table.h"
#include "preprocessor/preprocessor_internal.h"

namespace delta {

static std::string BlankKeywordMarkers(
    std::string_view text,
    const std::function<void(uint32_t, uint32_t)>& report) {
  std::string out(text);
  uint32_t line = 1;
  uint32_t column = 1;
  for (char& c : out) {
    if (c == kKeywordMarker) {
      report(line, column);
      c = ' ';
    }
    if (c == '\n') {
      line++;
      column = 1;
    } else {
      column++;
    }
  }
  return out;
}

Preprocessor::Preprocessor(SourceManager& src_mgr, DiagEngine& diag,
                           PreprocConfig config)
    : src_mgr_(src_mgr), diag_(diag), config_(std::move(config)) {
  for (const auto& [name, value] : config_.defines) {
    MacroDef def;
    def.name = name;
    def.body = BlankKeywordMarkers(value, [&](uint32_t, uint32_t) {
      diag_.Error(
          SourceLoc::None(),
          "unexpected character 0x01 in the value of command-line define '" +
              name + "'",
          Subclause("5.2"));
    });
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
  initial_macros_ = macros_;
}

void Preprocessor::DefinePredefined(std::string name, std::string body) {
  MacroDef def;
  def.name = std::move(name);
  def.body = std::move(body);
  macros_.Define(std::move(def));
}

std::string Preprocessor::Preprocess(uint32_t file_id) {
  auto content = src_mgr_.FileContent(file_id);
  recording_origins_ = true;
  auto output = ProcessSource(content, file_id, 0);
  recording_origins_ = false;
  ReportUnclosedConditionals();
  return output;
}

void Preprocessor::NoteOutputLine(uint32_t file_id, uint32_t line) {
  if (has_line_override_ && line > line_override_src_line_) {
    line = line_offset_ + (line - line_override_src_line_ - 1);
    file_id = line_file_override_id_;
  }
  line_origins_.push_back({file_id, line});
}

OutputMark Preprocessor::MarkOutput(const std::string& output) const {
  return {output.size(), line_origins_.size()};
}

void Preprocessor::NoteOutputLines(uint32_t file_id, uint32_t line,
                                   const std::string& output, OutputMark mark) {
  if (!recording_origins_) return;
  auto written = std::string_view(output).substr(mark.output_size);
  size_t newlines =
      static_cast<size_t>(std::count(written.begin(), written.end(), '\n'));
  size_t nested = line_origins_.size() - mark.origins_size;
  for (size_t i = nested; i < newlines; ++i) NoteOutputLine(file_id, line);
}

std::string Preprocessor::WithoutKeywordMarkers(std::string_view src,
                                                uint32_t file_id) {
  if (src.find(kKeywordMarker) == std::string_view::npos) return {};
  return BlankKeywordMarkers(src, [&](uint32_t line, uint32_t column) {
    diag_.Error({file_id, line, column},
                "unexpected character 0x01 in source text", Subclause("5.2"));
  });
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
      "__FILE__",
      "__LINE__",
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

bool IsDirectiveOtherThanValue(std::string_view name) {
  return IsCompilerDirective(name) && name != "__FILE__" && name != "__LINE__";
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
    if (!in_string && !in_triple && body[i] == '\\') {
      i = EndOfEscapedIdentifier(body, i);
      continue;
    }
    if (body[i] == '"' && (i == 0 || body[i - 1] != '\\')) {
      ProcessQuoteChar(body, i, in_string, in_triple);
    }
  }
  return in_string || in_triple;
}

bool StartsWithDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  if (trimmed.size() < dir.size() + 1) {
    return false;
  }
  if (trimmed[0] != '`') {
    return false;
  }
  return trimmed.substr(1, dir.size()) == dir;
}

std::string_view AfterDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Preprocessor::Trim(line);
  auto rest = trimmed.substr(1 + dir.size());
  return Preprocessor::Trim(rest);
}

std::pair<std::string_view, std::string_view> SplitFirstToken(
    std::string_view s) {
  size_t end = 0;
  while (end < s.size() && !std::isspace(static_cast<unsigned char>(s[end])))
    ++end;
  if (end >= s.size()) return {s, {}};
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

std::pair<std::string_view, std::string_view> SplitTimescaleArg(
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

std::pair<std::string_view, std::string_view> SplitQuotedArg(
    std::string_view s) {
  auto first = s.find('"');
  if (first == std::string_view::npos) return {s, {}};
  auto second = s.find('"', first + 1);
  if (second == std::string_view::npos) return {s, {}};
  auto end = second + 1;
  return {s.substr(0, end), Preprocessor::Trim(s.substr(end))};
}

static void PutCommentBody(std::string_view body, std::string& result,
                           std::vector<std::string>* comments) {
  if (comments == nullptr) {
    result.append(body.size(), ' ');
    return;
  }
  result += kCommentMark;
  result += std::to_string(comments->size());
  result += kCommentMark;
  comments->emplace_back(body);
}

static bool StripBlockCommentContent(std::string_view line, size_t& i,
                                     std::string& result,
                                     std::vector<std::string>* comments) {
  auto close = line.find("*/", i);
  size_t end = close == std::string_view::npos ? line.size() : close;
  PutCommentBody(line.substr(i, end - i), result, comments);
  i = end;
  if (close == std::string_view::npos) return false;
  result += "*/";
  i += 2;
  return true;
}

static void StripNormalChar(std::string_view line, size_t& i,
                            std::string& result, bool& in_block_comment,
                            std::vector<std::string>* comments) {
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '/') {
    result += "//";
    size_t end = std::min(line.find('\n', i + 2), line.size());
    PutCommentBody(line.substr(i + 2, end - i - 2), result, comments);
    i = end;
    return;
  }
  if (i + 1 < line.size() && line[i] == '/' && line[i + 1] == '*') {
    result += "/*";
    i += 2;
    in_block_comment = true;
    return;
  }
  result += line[i++];
}

bool AtTripleQuote(std::string_view line, size_t i) {
  return line.substr(i, 3) == "\"\"\"";
}

static void CopyTripleQuotedChar(std::string_view line, size_t& i,
                                 std::string& result, bool& in_triple_string) {
  if (AtTripleQuote(line, i)) {
    result += "\"\"\"";
    i += 3;
    in_triple_string = false;
    return;
  }
  if (line[i] == '\\') result += line[i++];
  if (i < line.size()) result += line[i++];
}

static bool CopyOpenTripleString(std::string_view& line, std::string& output,
                                 bool& in_triple_string) {
  bool was_open = in_triple_string;
  size_t i = 0;
  while (in_triple_string && i < line.size()) {
    CopyTripleQuotedChar(line, i, output, in_triple_string);
  }
  line.remove_prefix(i);
  return was_open;
}

static bool CopyStringLiteralChar(std::string_view line, size_t& i,
                                  std::string& result, bool& in_string,
                                  bool& in_triple_string) {
  if (!in_string && AtTripleQuote(line, i)) {
    result += "\"\"\"";
    i += 3;
    in_triple_string = true;
    return true;
  }
  if (line[i] == '\\') {
    size_t end = in_string ? i + 2 : EndOfEscapedIdentifier(line, i);
    result += line.substr(i, end - i);
    i = end;
    return true;
  }
  if (line[i] == '"') {
    in_string = !in_string;
    result += line[i++];
    return true;
  }
  if (!in_string) return false;
  result += line[i++];
  return true;
}

std::string StripComments(std::string_view line, bool& in_block_comment,
                          bool& in_triple_string,
                          std::vector<std::string>* comments) {
  std::string result;
  result.reserve(line.size());
  bool in_string = false;
  size_t i = 0;

  while (i < line.size()) {
    if (in_block_comment) {
      if (StripBlockCommentContent(line, i, result, comments)) {
        in_block_comment = false;
      }
      continue;
    }
    if (in_triple_string) {
      CopyTripleQuotedChar(line, i, result, in_triple_string);
      continue;
    }
    if (CopyStringLiteralChar(line, i, result, in_string, in_triple_string)) {
      continue;
    }
    StripNormalChar(line, i, result, in_block_comment, comments);
  }
  return result;
}

static bool OpensCommentMark(const std::string& text, size_t i) {
  return text[i] == kCommentMark &&
         std::isdigit(static_cast<unsigned char>(text[i + 1]));
}

void RestoreComments(std::string& text, size_t from,
                     const std::vector<std::string>& comments) {
  if (comments.empty()) return;
  std::string restored;
  restored.reserve(text.size() - from);
  size_t i = from;
  while (i < text.size()) {
    if (!OpensCommentMark(text, i)) {
      restored += text[i++];
      continue;
    }
    size_t index = 0;
    for (++i; std::isdigit(static_cast<unsigned char>(text[i])); ++i) {
      index = index * 10 + static_cast<size_t>(text[i] - '0');
    }
    restored += comments[index];
    ++i;
  }
  text.replace(from, std::string::npos, restored);
}

void Preprocessor::ExpandAndAppendLine(std::string_view line, uint32_t file_id,
                                       uint32_t line_num, std::string& output) {
  std::vector<std::string> comments;
  auto stripped =
      StripComments(line, in_block_comment_, in_triple_string_, &comments);
  auto conditioned =
      ExpandInlineConditionals(stripped, SourceLoc{file_id, line_num, 1});
  auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  size_t from = output.size();
  output.append(expanded);
  RestoreComments(output, from, comments);
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

static bool BacktickIntroducesDirective(std::string_view s, size_t i) {
  size_t start = i + 1;
  size_t end = start;
  while (end < s.size() && IsIdentChar(s[end])) ++end;
  return end > start && IsDirectiveOtherThanValue(s.substr(start, end - start));
}

static size_t FindMidLineDirective(std::string_view s) {
  auto state = StringLiteralState::kOutside;
  size_t i = 0;
  while (i < s.size()) {
    if (OutsideEveryString(state) && s[i] == '`' &&
        BacktickIntroducesDirective(s, i)) {
      return i;
    }
    i = StepOverStringSyntax(s, i, state);
  }
  return std::string_view::npos;
}

bool Preprocessor::ProcessBlockCommentLine(std::string_view line,
                                           uint32_t file_id, uint32_t line_num,
                                           int depth, std::string& output) {
  OutputMark mark = MarkOutput(output);
  auto close = line.find("*/");
  if (close == std::string_view::npos) {
    output.append(line);
    output.push_back('\n');
    NoteOutputLines(file_id, line_num, output, mark);
    return true;
  }
  output.append(line.substr(0, close + 2));
  in_block_comment_ = false;
  auto remainder = line.substr(close + 2);
  if (!Trim(remainder).empty()) {
    if (!ProcessDirective(remainder, file_id, line_num, depth, output)) {
      ExpandAndAppendLine(remainder, file_id, line_num, output);
    }
  }
  output.push_back('\n');
  NoteOutputLines(file_id, line_num, output, mark);
  return true;
}

void Preprocessor::SkipBlockCommentLine(std::string_view line, uint32_t file_id,
                                        uint32_t line_num, int depth,
                                        std::string& output) {
  OutputMark mark = MarkOutput(output);
  auto close = line.find("*/");
  if (close != std::string_view::npos) {
    in_block_comment_ = false;
    auto remainder = line.substr(close + 2);
    if (!Trim(remainder).empty()) {
      if (!ProcessDirective(remainder, file_id, line_num, depth, output)) {
        StripComments(remainder, in_block_comment_, in_triple_string_);
      }
    }
  }
  output.push_back('\n');
  NoteOutputLines(file_id, line_num, output, mark);
}

ActiveLineSplit ClassifyActiveLine(std::string_view stripped) {
  size_t dir_pos = FindDirectiveInStripped(stripped);
  if (dir_pos != std::string_view::npos)
    return {ActiveLineSplit::Kind::kLeadingDirective, dir_pos};
  size_t mid = FindMidLineDirective(stripped);
  if (mid != std::string_view::npos)
    return {ActiveLineSplit::Kind::kMidLineDirective, mid};
  return {ActiveLineSplit::Kind::kPlainText, 0};
}

struct PreprocLoopOps {
  std::function<bool()> in_block_comment;
  std::function<void(std::string_view)> continue_block_comment;
  std::function<bool(std::string_view)> run_directive;
  std::function<bool()> is_active;
  std::function<MacroUsageEnd(std::string_view)> end_of_macro_usage;
  std::function<bool(std::string_view&)> copy_open_string;
  std::function<void(std::string_view)> emit_active_line;
  std::function<void(std::string_view)> note_ignored_line;
  std::function<OutputMark()> mark_output;
  std::function<void(OutputMark)> note_output_lines;
};

static uint32_t ProcessOrdinaryLine(std::string_view line, LineCursor& cursor,
                                    const PreprocLoopOps& ops) {
  std::string joined;
  uint32_t usage_lines = 0;
  if (ops.is_active() && ops.copy_open_string(line)) {
    ops.emit_active_line(line);
    return usage_lines;
  }
  if (DefineSpansMultipleLines(line)) {
    uint32_t opened = cursor.line_num;
    joined = JoinDefineBody(cursor);
    uint32_t last = std::exchange(cursor.line_num, opened);
    ops.run_directive(joined);
    cursor.line_num = last;
    return usage_lines;
  }
  if (ops.is_active()) {
    usage_lines = JoinMacroUsage(cursor, ops.end_of_macro_usage, joined);
    if (usage_lines > 0) line = joined;
  }
  if (ops.run_directive(line)) return usage_lines;
  if (ops.is_active())
    ops.emit_active_line(line);
  else
    ops.note_ignored_line(line);
  return usage_lines;
}

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
      OutputMark mark = ops.mark_output();
      uint32_t usage_lines = ProcessOrdinaryLine(line, cursor, ops);
      output.push_back('\n');
      ops.note_output_lines(mark);
      line_num += usage_lines;
    }
    pos = eol + 1;
  }
}

void Preprocessor::ResetAnnouncementsAndRecoveredKeys() {
  key_public_key_value_next_ = false;
  key_block_value_next_ = false;
  data_decrypt_key_value_next_ = false;
  data_public_key_value_next_ = false;
  digest_public_key_value_next_ = false;
  digest_decrypt_key_value_next_ = false;
  digest_block_value_next_ = false;
  data_block_value_next_ = false;
  data_decrypt_key_.clear();
  digest_decrypt_key_.clear();
}

void Preprocessor::EndAccumulatedProtectPragmas() {
  ResetAnnouncementsAndRecoveredKeys();
  gathering_block_ = ProtectBlockKind::kNone;
  gathering_block_text_.clear();
  digest_target_ = ProtectDigestTarget();
}

static void EmitStrippedActiveLine(const std::string& stripped,
                                   bool inline_conditional,
                                   const ActiveLineEmit& emit,
                                   std::string& output) {
  if (inline_conditional) {
    emit.expand_and_emit(stripped);
    return;
  }
  EmitActiveLine(stripped, emit, output);
}

void Preprocessor::EmitCommentedActiveLine(std::string_view line,
                                           const ActiveLineEmit& emit,
                                           std::string& output) {
  std::vector<std::string> comments;
  auto stripped = StripComments(std::string(line), in_block_comment_,
                                in_triple_string_, &comments);
  if (!in_triple_string_ && EndsInContinuedQuotedString(stripped)) {
    in_continued_string_ = true;
  }
  size_t from = output.size();
  EmitStrippedActiveLine(stripped, HasInlineConditional(stripped), emit,
                         output);
  RestoreComments(output, from, comments);
}

std::string Preprocessor::ProcessSource(std::string_view src, uint32_t file_id,
                                        int depth) {
  if (depth > kMaxIncludeDepth) {
    diag_.Error({file_id, 1, 1}, "include depth exceeds maximum of 15",
                Subclause::None());
    return "";
  }

  std::string without_markers = WithoutKeywordMarkers(src, file_id);
  if (!without_markers.empty()) src = without_markers;

  uint32_t line_num = 0;
  std::string output;
  output.reserve(src.size());

  ActiveLineEmit emit;
  emit.expand_and_emit = [&](std::string_view fragment) {
    auto conditioned = ExpandInlineConditionals(
        std::string(fragment), SourceLoc{file_id, line_num, 1});
    auto expanded = ExpandInlineMacros(conditioned, file_id, line_num);
    TrackDesignElement(Trim(expanded));
    output.append(expanded);
  };
  emit.emit_directive_or_text = [&](std::string_view fragment) {
    if (!ProcessDirective(fragment, file_id, line_num, depth, output))
      emit.expand_and_emit(fragment);
  };
  emit.report_text_before_include = [&] {
    diag_.Error(
        {file_id, line_num, 1},
        "only white space or a comment may precede `include on its line",
        Subclause("22.4"));
  };

  PreprocLoopOps ops;
  ops.in_block_comment = [&] { return in_block_comment_; };
  ops.is_active = [&] { return IsActive(); };
  ops.end_of_macro_usage = [&](std::string_view text) {
    return EndOfMacroUsage(text);
  };
  ops.copy_open_string = [&](std::string_view& line) {
    return CopyOpenTripleString(line, output, in_triple_string_) ||
           CopyContinuedQuotedString(line, output, in_continued_string_);
  };
  ops.continue_block_comment = [&](std::string_view line) {
    if (IsActive())
      ProcessBlockCommentLine(line, file_id, line_num, depth, output);
    else
      SkipBlockCommentLine(line, file_id, line_num, depth, output);
  };
  ops.run_directive = [&](std::string_view line) {
    return TookAnnouncedValue(line, {file_id, line_num, 1}, depth, output) ||
           ProcessDirective(line, file_id, line_num, depth, output);
  };
  ops.emit_active_line = [&](std::string_view line) {
    EmitCommentedActiveLine(line, emit, output);
  };
  ops.note_ignored_line = [&](std::string_view line) {
    NoteIgnoredLine(line, {file_id, line_num, 1});
  };
  ops.mark_output = [&] { return MarkOutput(output); };
  ops.note_output_lines = [&](OutputMark mark) {
    NoteOutputLines(file_id, line_num, output, mark);
  };

  RunPreprocLoop(src, line_num, ops, output);
  FinishProtectedReading(depth, output);
  return output;
}

void Preprocessor::FinishProtectedReading(int depth, std::string& output) {
  FinishGatheredProtectBlock(depth, output);
  ReadRecoveredText(output);
}

void Preprocessor::OutputText(std::string_view text, uint32_t file_id,
                              uint32_t line_num, std::string& output) {
  if (Trim(text).empty()) return;
  std::vector<std::string> comments;
  auto stripped =
      StripComments(text, in_block_comment_, in_triple_string_, &comments);
  auto expanded = ExpandInlineMacros(stripped, file_id, line_num);
  TrackDesignElement(Trim(expanded));
  size_t from = output.size();
  output.append(expanded);
  RestoreComments(output, from, comments);
}

void Preprocessor::OutputPreExpanded(std::string_view text,
                                     std::string& output) {
  if (Trim(text).empty()) return;
  std::vector<std::string> comments;
  auto stripped =
      StripComments(text, in_block_comment_, in_triple_string_, &comments);
  TrackDesignElement(Trim(std::string_view(stripped)));
  size_t from = output.size();
  output.append(stripped);
  RestoreComments(output, from, comments);
}

}  // namespace delta
