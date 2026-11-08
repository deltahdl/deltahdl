#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/standard_pragmas.h"

namespace delta {

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
                                             SourceLoc loc,
                                             Subclause subclause) {
  if (design_element_depth_ == 0) return false;
  std::string msg = "`";
  msg.append(directive_name);
  msg.append(" illegal inside a design element");
  diag_.Error(loc, msg, subclause);
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
  default_decay_time_is_real_ = false;
  default_trireg_strength_ = 0;
  has_default_trireg_strength_ = false;
  delay_mode_directive_ = DelayModeDirective::kNone;
}

bool Preprocessor::ProcessDelayModeDirective(std::string_view line,
                                             SourceLoc loc) {
  if (StartsWithDirective(line, "delay_mode_distributed")) {
    if (RejectInsideDesignElement("delay_mode_distributed", loc,
                                  Subclause("E.4")))
      return true;
    delay_mode_directive_ = DelayModeDirective::kDistributed;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_path")) {
    if (RejectInsideDesignElement("delay_mode_path", loc, Subclause("E.5")))
      return true;
    delay_mode_directive_ = DelayModeDirective::kPath;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_unit")) {
    if (RejectInsideDesignElement("delay_mode_unit", loc, Subclause("E.6")))
      return true;
    delay_mode_directive_ = DelayModeDirective::kUnit;
    return true;
  }
  if (StartsWithDirective(line, "delay_mode_zero")) {
    if (RejectInsideDesignElement("delay_mode_zero", loc, Subclause("E.7")))
      return true;
    delay_mode_directive_ = DelayModeDirective::kZero;
    return true;
  }
  return false;
}

static bool DirectiveKeywordIsWholeWord(std::string_view line,
                                        std::string_view keyword) {
  auto trimmed = Preprocessor::Trim(line);
  size_t after_keyword = 1 + keyword.size();
  if (trimmed.size() <= after_keyword) return true;
  return !IsIdentChar(trimmed[after_keyword]);
}

static bool StartsWithCellDirective(std::string_view line,
                                    std::string_view keyword) {
  return StartsWithDirective(line, keyword) &&
         DirectiveKeywordIsWholeWord(line, keyword);
}

bool StartsWithPragmaDirective(std::string_view line) {
  return StartsWithDirective(line, "pragma") &&
         DirectiveKeywordIsWholeWord(line, "pragma");
}

enum class PragmaTokenKind : std::uint8_t {
  kSimpleIdentifier,
  kEscapedIdentifier,
  kNumber,
  kString,
  kOpenParen,
  kCloseParen,
  kComma,
  kEquals,
};

struct PragmaToken {
  PragmaTokenKind kind;
  std::string_view text;
};

using PragmaTokens = std::vector<PragmaToken>;

static size_t ScanPragmaIdentifier(std::string_view s, size_t i) {
  ++i;
  while (i < s.size() && IsIdentChar(s[i])) ++i;
  return i;
}

static bool StartsPragmaNumber(std::string_view s, size_t i) {
  if (std::isdigit(static_cast<unsigned char>(s[i]))) return true;
  return s[i] == '\'' && i + 1 < s.size() &&
         std::isalnum(static_cast<unsigned char>(s[i + 1]));
}

static size_t ScanPragmaNumber(std::string_view s, size_t i) {
  while (i < s.size()) {
    char c = s[i];
    if (IsIdentChar(c) || c == '\'' || c == '.') {
      ++i;
      continue;
    }
    if ((c == '+' || c == '-') && (s[i - 1] == 'e' || s[i - 1] == 'E')) {
      ++i;
      continue;
    }
    break;
  }
  return i;
}

static size_t ScanPragmaString(std::string_view s, size_t i) {
  if (s.compare(i, 3, "\"\"\"") == 0) {
    size_t close = s.find("\"\"\"", i + 3);
    if (close == std::string_view::npos) return std::string_view::npos;
    return close + 3;
  }
  ++i;
  while (i < s.size()) {
    if (s[i] == '\\' && i + 1 < s.size()) {
      i += 2;
      continue;
    }
    if (s[i] == '"') return i + 1;
    ++i;
  }
  return std::string_view::npos;
}

static size_t ScanPragmaEscapedIdentifier(std::string_view s, size_t i) {
  ++i;
  while (i < s.size() && !std::isspace(static_cast<unsigned char>(s[i]))) ++i;
  return i;
}

enum class PragmaScanStep : std::uint8_t {
  kAdvanced,
  kStop,
  kInvalid,
  kNotHandled
};

static PragmaScanStep ScanPragmaWordToken(std::string_view s, size_t& i,
                                          PragmaTokens& out) {
  size_t start = i;
  char c = s[i];
  if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
    i = ScanPragmaIdentifier(s, i);
    out.push_back(
        {PragmaTokenKind::kSimpleIdentifier, s.substr(start, i - start)});
    return PragmaScanStep::kAdvanced;
  }
  if (c == '\\') {
    size_t end = ScanPragmaEscapedIdentifier(s, i);
    if (end == i + 1) return PragmaScanStep::kInvalid;
    i = end;
    out.push_back(
        {PragmaTokenKind::kEscapedIdentifier, s.substr(start, i - start)});
    return PragmaScanStep::kAdvanced;
  }
  if (StartsPragmaNumber(s, i)) {
    i = ScanPragmaNumber(s, i);
    out.push_back({PragmaTokenKind::kNumber, s.substr(start, i - start)});
    return PragmaScanStep::kAdvanced;
  }
  if (c == '"') {
    size_t end = ScanPragmaString(s, i);
    if (end == std::string_view::npos) return PragmaScanStep::kInvalid;
    i = end;
    out.push_back({PragmaTokenKind::kString, s.substr(start, i - start)});
    return PragmaScanStep::kAdvanced;
  }
  return PragmaScanStep::kNotHandled;
}

static PragmaScanStep ScanPragmaCommentToken(std::string_view s, size_t& i,
                                             bool& block_comment_open) {
  if (s[i] != '/' || i + 1 >= s.size()) return PragmaScanStep::kNotHandled;
  if (s[i + 1] == '/') return PragmaScanStep::kStop;
  if (s[i + 1] != '*') return PragmaScanStep::kNotHandled;
  size_t close = s.find("*/", i + 2);
  if (close == std::string_view::npos) {
    block_comment_open = true;
    return PragmaScanStep::kStop;
  }
  i = close + 2;
  return PragmaScanStep::kAdvanced;
}

static bool PushPragmaPunctuation(std::string_view s, size_t i,
                                  PragmaTokens& out) {
  std::string_view text = s.substr(i, 1);
  switch (s[i]) {
    case '(':
      out.push_back({PragmaTokenKind::kOpenParen, text});
      return true;
    case ')':
      out.push_back({PragmaTokenKind::kCloseParen, text});
      return true;
    case ',':
      out.push_back({PragmaTokenKind::kComma, text});
      return true;
    case '=':
      out.push_back({PragmaTokenKind::kEquals, text});
      return true;
    default:
      return false;
  }
}

static bool TokenizePragma(std::string_view s, PragmaTokens& out,
                           bool& block_comment_open) {
  size_t i = 0;
  while (i < s.size()) {
    if (std::isspace(static_cast<unsigned char>(s[i]))) {
      ++i;
      continue;
    }
    PragmaScanStep step = ScanPragmaWordToken(s, i, out);
    if (step == PragmaScanStep::kInvalid) return false;
    if (step == PragmaScanStep::kAdvanced) continue;

    step = ScanPragmaCommentToken(s, i, block_comment_open);
    if (step == PragmaScanStep::kStop) break;
    if (step == PragmaScanStep::kAdvanced) continue;

    if (!PushPragmaPunctuation(s, i, out)) return false;
    ++i;
  }
  return true;
}

static bool ParsePragmaExpressionList(
    const PragmaTokens& toks, size_t& i,
    std::vector<PragmaKeywordExpression>* keywords);

static bool ParsePragmaValue(const PragmaTokens& toks, size_t& i) {
  if (i >= toks.size()) return false;
  if (toks[i].kind == PragmaTokenKind::kOpenParen) {
    ++i;
    if (!ParsePragmaExpressionList(toks, i, nullptr)) return false;
    if (i >= toks.size() || toks[i].kind != PragmaTokenKind::kCloseParen) {
      return false;
    }
    ++i;
    return true;
  }
  if (toks[i].kind == PragmaTokenKind::kNumber ||
      toks[i].kind == PragmaTokenKind::kString ||
      toks[i].kind == PragmaTokenKind::kSimpleIdentifier ||
      toks[i].kind == PragmaTokenKind::kEscapedIdentifier) {
    ++i;
    return true;
  }
  return false;
}

static std::string_view SpannedText(const PragmaTokens& toks, size_t first,
                                    size_t last) {
  const char* start = toks[first].text.data();
  std::string_view final_token = toks[last - 1].text;
  size_t size =
      static_cast<size_t>(final_token.data() - start) + final_token.size();
  return {start, size};
}

static bool ParsePragmaExpression(
    const PragmaTokens& toks, size_t& i,
    std::vector<PragmaKeywordExpression>* keywords) {
  if (i >= toks.size()) return false;
  bool has_keyword = toks[i].kind == PragmaTokenKind::kSimpleIdentifier;
  bool has_value = has_keyword && i + 1 < toks.size() &&
                   toks[i + 1].kind == PragmaTokenKind::kEquals;
  if (keywords != nullptr && has_keyword) {
    keywords->push_back({toks[i].text, {}, has_value, {}});
  }
  if (has_value) {
    i += 2;
    size_t value_start = i;
    if (!ParsePragmaValue(toks, i)) return false;
    if (keywords != nullptr && i == value_start + 1) {
      keywords->back().value = toks[value_start].text;
    }
    if (keywords != nullptr && i > value_start + 1) {
      keywords->back().value_list = SpannedText(toks, value_start, i);
    }
    return true;
  }
  return ParsePragmaValue(toks, i);
}

static bool ParsePragmaExpressionList(
    const PragmaTokens& toks, size_t& i,
    std::vector<PragmaKeywordExpression>* keywords) {
  if (!ParsePragmaExpression(toks, i, keywords)) return false;
  while (i < toks.size() && toks[i].kind == PragmaTokenKind::kComma) {
    ++i;
    if (!ParsePragmaExpression(toks, i, keywords)) return false;
  }
  return true;
}

bool Preprocessor::ProcessSimpleStateDirective(std::string_view line,
                                               SourceLoc loc, int depth,
                                               std::string& output) {
  if (StartsWithCellDirective(line, "endcelldefine")) {
    in_celldefine_ = false;
    ProcessDirectiveRemainder(line, "endcelldefine", loc, depth, output);
    return true;
  }
  if (StartsWithCellDirective(line, "celldefine")) {
    in_celldefine_ = true;
    ProcessDirectiveRemainder(line, "celldefine", loc, depth, output);
    return true;
  }
  if (StartsWithPragmaDirective(line)) {
    std::string expanded = ExpandInlineMacros(AfterDirective(line, "pragma"),
                                              loc.file_id, loc.line);
    HandlePragma(expanded, loc);
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  return false;
}

PragmaReading ReadPragmaDirective(std::string_view rest) {
  PragmaReading reading;
  PragmaTokens toks;
  if (!TokenizePragma(rest, toks, reading.block_comment_open)) {
    reading.error = "`pragma directive contains an illegal token";
  } else if (toks.empty()) {
    reading.error = "`pragma requires a pragma_name";
  } else if (toks.front().kind != PragmaTokenKind::kSimpleIdentifier) {
    reading.error = "`pragma pragma_name must be a simple identifier";
  } else {
    reading.name = toks.front().text;
    size_t i = 1;
    if (i != toks.size() &&
        (!ParsePragmaExpressionList(toks, i, &reading.keywords) ||
         i != toks.size())) {
      reading.error = "malformed pragma_expression after pragma_name";
    }
  }
  return reading;
}

void Preprocessor::HandlePragma(std::string_view rest, SourceLoc loc) {
  PragmaReading reading = ReadPragmaDirective(rest);
  if (reading.block_comment_open) in_block_comment_ = true;
  if (!reading.error.empty()) {
    diag_.Error(loc, std::string(reading.error), Subclause("22.11"));
    return;
  }
  const std::vector<PragmaKeywordExpression>& keywords = reading.keywords;
  std::string_view name = reading.name;
  if (name == kProtectPragmaName) {
    ApplyProtectKeywords(keywords, loc);
    return;
  }
  if (name == kResetPragmaName) {
    for (const auto& expr : keywords) ResetPragma(expr.keyword);
    return;
  }
  if (name == kResetallPragmaName) ResetAllPragmas();
}

void Preprocessor::ResetAllPragmas() {
  for (std::string_view recognized : RecognizedPragmaNames()) {
    ResetPragma(recognized);
  }
}

void Preprocessor::ResetPragma(std::string_view pragma_name) {
  if (!IsRecognizedPragmaName(pragma_name)) return;
  protect_keywords_.Reset();
  ResetAnnouncementsAndRecoveredKeys();
}

bool Preprocessor::ProcessExpandedStateDirective(std::string_view line,
                                                 SourceLoc loc,
                                                 uint32_t file_id,
                                                 uint32_t line_num,
                                                 std::string& output) {
  if (StartsWithDirective(line, "timescale")) {
    if (RejectInsideDesignElement("timescale", loc, Subclause("22.7")))
      return true;
    auto rest = AfterDirective(line, "timescale");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [ts_arg, remainder] = SplitTimescaleArg(expanded);
    HandleTimescale(ts_arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "default_nettype")) {
    if (RejectInsideDesignElement("default_nettype", loc, Subclause("22.8")))
      return true;
    auto rest = AfterDirective(line, "default_nettype");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleDefaultNettype(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "unconnected_drive")) {
    if (RejectInsideDesignElement("unconnected_drive", loc, Subclause("22.9")))
      return true;
    auto rest = AfterDirective(line, "unconnected_drive");
    auto expanded = ExpandInlineMacros(rest, file_id, line_num);
    auto [arg, remainder] = SplitFirstToken(expanded);
    HandleUnconnectedDrive(arg, loc);
    OutputPreExpanded(remainder, output);
    return true;
  }
  if (StartsWithDirective(line, "nounconnected_drive")) {
    if (RejectInsideDesignElement("nounconnected_drive", loc,
                                  Subclause("22.9")))
      return true;
    unconnected_drive_ = NetType::kWire;
    auto [arg, remainder] =
        SplitFirstToken(AfterDirective(line, "nounconnected_drive"));
    if (arg == "pull0" || arg == "pull1") {
      diag_.Error(loc,
                  "`nounconnected_drive takes no argument; '" +
                      std::string(arg) + "' was given",
                  Subclause("22.9"));
      OutputText(remainder, file_id, line_num, output);
      return true;
    }
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
    if (RejectInsideDesignElement("resetall", loc, Subclause("22.3")))
      return true;
    ResetDirectiveState();
    OutputRemainder(line, "resetall", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "default_decay_time")) {
    HandleDefaultDecayTime(AfterDirective(line, "default_decay_time"), loc);
    return true;
  }
  if (StartsWithDirective(line, "default_trireg_strength")) {
    HandleDefaultTriregStrength(AfterDirective(line, "default_trireg_strength"),
                                loc);
    return true;
  }
  return ProcessDelayModeDirective(line, loc);
}

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc,
                                         int depth, std::string& output) {
  if (ProcessSimpleStateDirective(line, loc, depth, output)) return true;
  if (ProcessExpandedStateDirective(line, loc, loc.file_id, loc.line, output))
    return true;
  return ProcessMiscStateDirective(line, loc, loc.file_id, loc.line, output);
}

static bool StartsWithUndefDirective(std::string_view line) {
  if (!StartsWithDirective(line, "undef")) return false;
  auto trimmed = Preprocessor::Trim(line);
  constexpr size_t kAfterKeyword = 1 + 5;
  if (trimmed.size() <= kAfterKeyword) return true;
  return !IsIdentChar(trimmed[kAfterKeyword]);
}

static bool StartsWithUndefineAllDirective(std::string_view line) {
  if (!StartsWithDirective(line, "undefineall")) return false;
  auto trimmed = Preprocessor::Trim(line);
  constexpr size_t kAfterKeyword = 1 + 11;
  if (trimmed.size() <= kAfterKeyword) return true;
  return !IsIdentChar(trimmed[kAfterKeyword]);
}

static bool StartsTextMacroIdentifier(std::string_view text) {
  return std::isalpha(static_cast<unsigned char>(text[0])) != 0 ||
         text[0] == '_' || text[0] == '\\';
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

static bool StartsWithKeywordsDirective(std::string_view line,
                                        std::string_view keyword) {
  return StartsWithDirective(line, keyword) &&
         DirectiveKeywordIsWholeWord(line, keyword);
}

bool Preprocessor::ProcessKeywordsDirective(std::string_view line,
                                            SourceLoc loc, uint32_t file_id,
                                            uint32_t line_num,
                                            std::string& output) {
  if (StartsWithKeywordsDirective(line, "begin_keywords")) {
    if (RejectInsideDesignElement("begin_keywords", loc, Subclause("22.14")))
      return true;
    auto rest = AfterDirective(line, "begin_keywords");
    auto [bk_arg, remainder] = SplitQuotedArg(rest);
    HandleBeginKeywords(bk_arg, loc, output);
    OutputText(remainder, file_id, line_num, output);
    return true;
  }
  if (StartsWithKeywordsDirective(line, "end_keywords")) {
    if (RejectInsideDesignElement("end_keywords", loc, Subclause("22.14")))
      return true;
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

void Preprocessor::ProcessUndefDirective(std::string_view line, SourceLoc loc,
                                         std::string& output) {
  auto trimmed_rest = Trim(AfterDirective(line, "undef"));
  size_t name_end = FindUndefNameEnd(trimmed_rest);
  if (name_end == 0 || !StartsTextMacroIdentifier(trimmed_rest)) {
    if (IsActive())
      diag_.Error(loc, "`undef requires a text macro name",
                  Subclause("22.5.2"));
    return;
  }
  HandleUndef(trimmed_rest.substr(0, name_end), loc);
  if (IsActive()) {
    OutputText(Trim(trimmed_rest.substr(name_end)), loc.file_id, loc.line,
               output);
  }
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
  if (StartsWithUndefineAllDirective(line)) {
    if (IsActive()) {
      macros_.UndefineAll();
      OutputRemainder(line, "undefineall", file_id, line_num, output);
    }
    return true;
  }
  if (StartsWithUndefDirective(line)) {
    ProcessUndefDirective(line, loc, output);
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
  SourceLoc loc{file_id, line_num, 1};
  if (StartsWithDirective(line, "ifdef")) {
    HandleIfdef(AfterDirective(line, "ifdef"), false, loc);
    return true;
  }
  if (StartsWithDirective(line, "ifndef")) {
    HandleIfdef(AfterDirective(line, "ifndef"), true, loc);
    return true;
  }
  if (StartsWithDirective(line, "elsif")) {
    HandleElsif(AfterDirective(line, "elsif"), loc);
    return true;
  }
  if (StartsWithDirective(line, "else")) {
    HandleElse(loc);

    if (IsActive()) OutputRemainder(line, "else", file_id, line_num, output);
    return true;
  }
  if (StartsWithDirective(line, "endif")) {
    HandleEndif(loc);

    if (IsActive()) OutputRemainder(line, "endif", file_id, line_num, output);
    return true;
  }
  return false;
}

}  // namespace delta
