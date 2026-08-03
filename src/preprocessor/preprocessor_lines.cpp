#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <sstream>

#include "preprocessor/preprocessor.h"
#include "preprocessor/preprocessor_internal.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

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
                                             SourceLoc loc) {
  if (design_element_depth_ == 0) return false;
  std::string msg = "`";
  msg.append(directive_name);
  msg.append(" illegal inside a design element");
  diag_.Error(loc, msg, Clause::Unread());
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

// A directive keyword ends where the identifier does: a name character sitting
// flush against it belongs to a longer name, so `celldefine_region is a usage
// of the macro celldefine_region rather than the `celldefine directive plus
// stray text.
static bool DirectiveKeywordIsWholeWord(std::string_view line,
                                        std::string_view keyword) {
  auto trimmed = Preprocessor::Trim(line);
  size_t after_keyword = 1 + keyword.size();  // backtick + keyword
  if (trimmed.size() <= after_keyword) return true;
  return !IsIdentChar(trimmed[after_keyword]);
}

// §22.10 spells these two directives as the bare keywords `celldefine and
// `endcelldefine; neither takes an operand. A line that only looks like one of
// them because a macro name happens to start the same way must not open or
// close a cell-module region.
static bool StartsWithCellDirective(std::string_view line,
                                    std::string_view keyword) {
  return StartsWithDirective(line, keyword) &&
         DirectiveKeywordIsWholeWord(line, keyword);
}

// Syntax 22-8 separates the `pragma keyword from the pragma_name that follows
// it, so `pragma_name is a usage of the macro pragma_name and not this
// directive carrying the pragma_name "_name".
static bool StartsWithPragmaDirective(std::string_view line) {
  return StartsWithDirective(line, "pragma") &&
         DirectiveKeywordIsWholeWord(line, "pragma");
}

// Syntax 22-8 gives `pragma a grammar of its own instead of a single operand:
// a pragma_name followed by an optional comma-separated pragma_expression
// list. The expressions are spelled with a handful of lexical shapes and the
// punctuation that joins them, so a small dedicated tokenizer covers the whole
// directive. A pragma_value may be any identifier, but a pragma_name and a
// pragma_keyword are restricted to the simple form, so the two identifier
// flavors are kept apart here rather than merged.
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

// A token carries its spelling beside its kind. The grammar alone settles
// whether a directive is well formed, but which specification the directive
// belongs to is the pragma_name, and what an expression asks that
// specification for is the pragma_keyword, so both have to be readable.
struct PragmaToken {
  PragmaTokenKind kind;
  std::string_view text;
};

using PragmaTokens = std::vector<PragmaToken>;

// A simple_identifier opens with a letter or underscore and continues with
// identifier characters; '$' is legal only after the first one, which is
// exactly what IsIdentChar admits.
static size_t ScanPragmaIdentifier(std::string_view s, size_t i) {
  ++i;
  while (i < s.size() && IsIdentChar(s[i])) ++i;
  return i;
}

// A number token opens with a digit, or with the tick of a based literal whose
// size was left off ('h1F) or of an unbased unsized literal ('0).
static bool StartsPragmaNumber(std::string_view s, size_t i) {
  if (std::isdigit(static_cast<unsigned char>(s[i]))) return true;
  return s[i] == '\'' && i + 1 < s.size() &&
         std::isalnum(static_cast<unsigned char>(s[i + 1]));
}

// A pragma_value number may carry a size and a base, a decimal point, or an
// exponent, so consume the characters those spellings use. The sign of an
// exponent is part of the number; a sign anywhere else is not.
static size_t ScanPragmaNumber(std::string_view s, size_t i) {
  while (i < s.size()) {
    char c = s[i];
    if (IsIdentChar(c) || c == '\'' || c == '.') {
      ++i;
      continue;
    }
    if ((c == '+' || c == '-') && i > 0 &&
        (s[i - 1] == 'e' || s[i - 1] == 'E')) {
      ++i;
      continue;
    }
    break;
  }
  return i;
}

// Returns the index just past the closing quote, or npos when the string
// literal runs off the end of the directive. A triple-quoted literal closes
// only on the next triple quote, so a single quote written inside one is
// ordinary content rather than a terminator.
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

// An escaped identifier runs from the backslash to the next whitespace
// character.
static size_t ScanPragmaEscapedIdentifier(std::string_view s, size_t i) {
  ++i;
  while (i < s.size() && !std::isspace(static_cast<unsigned char>(s[i]))) ++i;
  return i;
}

// Returns false when the text holds a character no pragma token may start
// with -- a '$'-led system name, for instance, which is neither an identifier
// nor a number nor a string. `block_comment_open` is set when the directive
// line ends inside a block comment, which the caller has to carry forward.
// What scanning one pragma token asks the tokenizer to do next.
enum class PragmaScanStep : std::uint8_t {
  kAdvanced,   // a token was consumed; carry on
  kStop,       // the directive text ends here
  kInvalid,    // the text is not a well-formed pragma
  kNotHandled  // this scanner does not recognize the character
};

// The identifier, number, and string forms a pragma expression list may hold.
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
    // A lone backslash names nothing.
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

// A comment is not part of the expression list. A one-line comment ends the
// directive text, and so does a block comment left open at the end of the line;
// a closed one is simply skipped over.
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

// The punctuation that joins the expressions of a pragma. Anything else is not
// part of the directive's grammar.
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

// `keywords`, when not null, collects the pragma_keyword of each expression
// the caller is walking, and the pragma_value written against it, in the order
// the expressions are written. It is null for the expressions nested inside a
// parenthesized pragma_value, because those qualify the value rather than the
// directive.
static bool ParsePragmaExpressionList(
    const PragmaTokens& toks, size_t& i,
    std::vector<PragmaKeywordExpression>* keywords);

// pragma_value ::= ( pragma_expression { , pragma_expression } )
//                | number | string | identifier
static bool ParsePragmaValue(const PragmaTokens& toks, size_t& i) {
  if (i >= toks.size()) return false;
  if (toks[i].kind == PragmaTokenKind::kOpenParen) {
    ++i;
    // The parenthesized form holds a list, not an optional one, so an empty
    // pair of parentheses is not a pragma_value.
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

// The directive text that the tokens from `first` up to `last` were scanned
// out of, as one run. Every token is a view into the same directive text, so
// the run from where the first one starts to where the last one ends is the
// text those tokens were written as, spacing and punctuation included.
static std::string_view SpannedText(const PragmaTokens& toks, size_t first,
                                    size_t last) {
  if (first >= last || last > toks.size()) return {};
  const char* start = toks[first].text.data();
  std::string_view final_token = toks[last - 1].text;
  size_t size =
      static_cast<size_t>(final_token.data() - start) + final_token.size();
  return {start, size};
}

// pragma_expression ::= pragma_keyword | pragma_keyword = pragma_value
//                     | pragma_value
// A lone simple identifier satisfies both the bare-keyword alternative and the
// identifier pragma_value, so only the '=' lookahead has to be decided here.
// The left side of an '=' is a pragma_keyword, which admits the simple form
// only.
static bool ParsePragmaExpression(
    const PragmaTokens& toks, size_t& i,
    std::vector<PragmaKeywordExpression>* keywords) {
  if (i >= toks.size()) return false;
  // A pragma_keyword is a simple identifier, whichever alternative it came
  // from, so the two spellings that expose one are the identifier standing
  // alone and the identifier on the left of an '='.
  bool has_keyword = toks[i].kind == PragmaTokenKind::kSimpleIdentifier;
  // The '=' is what settles which of the two spellings the expression was
  // written in, whatever the value after it turns out to look like, so it is
  // read before the expression is recorded rather than off the value.
  bool has_value = has_keyword && i + 1 < toks.size() &&
                   toks[i + 1].kind == PragmaTokenKind::kEquals;
  if (keywords != nullptr && has_keyword) {
    keywords->push_back({toks[i].text, {}, has_value, {}});
  }
  if (has_value) {
    i += 2;
    size_t value_start = i;
    if (!ParsePragmaValue(toks, i)) return false;
    // A value spelled as one token is a value the keyword can be said to
    // carry. A parenthesized one is a list of further expressions, and reading
    // it as the keyword's value would name only its opening parenthesis.
    if (keywords != nullptr && i == value_start + 1) {
      keywords->back().value = toks[value_start].text;
    }
    // The list itself is what a keyword defined with a parenthesized value
    // records, so it is collected whole -- from the opening parenthesis to the
    // closing one, as the directive spelled the text between them.
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
    // The directive text is ordinary source as far as 22.5.1 is concerned, so
    // macro usages inside it are substituted before the pragma grammar sees
    // it, the same way `timescale and `default_nettype treat their operands.
    std::string expanded = ExpandInlineMacros(AfterDirective(line, "pragma"),
                                              loc.file_id, loc.line);
    HandlePragma(expanded, loc, depth, output);
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  return false;
}

// Checks the directive against Syntax 22-8 and consumes it. The pragma_name
// is what identifies the specification, so it is mandatory and must be a
// simple_identifier; the pragma_expression list that qualifies it is optional.
// A pragma_name this implementation does not recognize leaves the
// interpretation of the surrounding source text alone, which for the
// preprocessor means the directive line contributes no output and changes no
// directive state. The protect name is the one this implementation does
// recognize: it is reserved for describing protected envelopes, so its
// expressions -- and no other pragma's, however they are spelled -- decide
// which regions of text an envelope covers.
void Preprocessor::HandlePragma(std::string_view rest, SourceLoc loc, int depth,
                                std::string& output) {
  PragmaTokens toks;
  bool block_comment_open = false;
  bool tokenized = TokenizePragma(rest, toks, block_comment_open);
  // The directive ends where the comment begins, but the comment itself keeps
  // running, so the lines after it are not source text either.
  if (block_comment_open) in_block_comment_ = true;
  if (!tokenized) {
    diag_.Error(loc, "`pragma directive contains an illegal token",
                Clause::Unread());
    return;
  }
  if (toks.empty()) {
    diag_.Error(loc, "`pragma requires a pragma_name", Clause::Unread());
    return;
  }
  if (toks.front().kind != PragmaTokenKind::kSimpleIdentifier) {
    diag_.Error(loc, "`pragma pragma_name must be a simple identifier",
                Clause::Unread());
    return;
  }
  std::vector<PragmaKeywordExpression> keywords;
  size_t i = 1;
  if (i != toks.size()) {
    if (!ParsePragmaExpressionList(toks, i, &keywords) || i != toks.size()) {
      diag_.Error(loc, "malformed pragma_expression after pragma_name",
                  Clause::Unread());
      return;
    }
  }
  if (toks.front().text == kProtectPragmaName) {
    ApplyProtectKeywords(keywords, loc, depth, output);
  }
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

// Syntax 22-4 spells the directive as the keyword `undef followed by a
// separate text_macro_identifier. A name character sitting directly against
// the keyword therefore belongs to a longer macro name (`undefX is a usage of
// the macro undefX), so such a line is not this directive at all.
static bool StartsWithUndefDirective(std::string_view line) {
  if (!StartsWithDirective(line, "undef")) return false;
  auto trimmed = Preprocessor::Trim(line);
  constexpr size_t kAfterKeyword = 1 + 5;  // backtick + "undef"
  if (trimmed.size() <= kAfterKeyword) return true;
  return !IsIdentChar(trimmed[kAfterKeyword]);
}

// §22.5.3 spells this directive as the bare keyword `undefineall, which takes
// no arguments at all. A name character sitting directly against the keyword
// therefore belongs to a longer macro name — `undefineall_saved is a usage of
// the macro undefineall_saved — so such a line is not this directive and must
// not wipe the macro table.
static bool StartsWithUndefineAllDirective(std::string_view line) {
  if (!StartsWithDirective(line, "undefineall")) return false;
  auto trimmed = Preprocessor::Trim(line);
  constexpr size_t kAfterKeyword = 1 + 11;  // backtick + "undefineall"
  if (trimmed.size() <= kAfterKeyword) return true;
  return !IsIdentChar(trimmed[kAfterKeyword]);
}

// §5.6 opens a simple_identifier with a letter or an underscore and an
// escaped_identifier with a backslash. Syntax 22-4 admits only an identifier
// after the keyword, so an operand starting with anything else — a digit, a
// dollar sign, punctuation — is not a text_macro_identifier at all.
static bool StartsTextMacroIdentifier(std::string_view text) {
  if (text.empty()) return false;
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

// Syntax 22-10 spells both halves of the pair as whole directive keywords:
// `begin_keywords is followed by a quoted version_specifier and `end_keywords
// takes no operand at all. A name character flush against either keyword is
// therefore part of a longer macro name, so `end_keywords_saved is a use of
// the macro end_keywords_saved and not this directive plus stray text.
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
    if (RejectInsideDesignElement("begin_keywords", loc)) return true;
    auto rest = AfterDirective(line, "begin_keywords");
    auto [bk_arg, remainder] = SplitQuotedArg(rest);
    HandleBeginKeywords(bk_arg, loc, output);
    OutputText(remainder, file_id, line_num, output);
    return true;
  }
  if (StartsWithKeywordsDirective(line, "end_keywords")) {
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

// Syntax 22-4 makes the text_macro_identifier part of the `undef directive, so
// a bare `undef, or one handed something that is not an identifier, names no
// macro to remove.
void Preprocessor::ProcessUndefDirective(std::string_view line, SourceLoc loc,
                                         std::string& output) {
  auto trimmed_rest = Trim(AfterDirective(line, "undef"));
  size_t name_end = FindUndefNameEnd(trimmed_rest);
  if (name_end == 0 || !StartsTextMacroIdentifier(trimmed_rest)) {
    if (IsActive())
      diag_.Error(loc, "`undef requires a text macro name", Clause::Unread());
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
    // The rule reaches macros defined within the compilation unit, and text
    // excluded by a conditional never becomes part of it. Wiping the table
    // from a branch that was compiled away would let a directive that is not
    // in the source description take effect, so gate it like `define/`undef.
    if (IsActive()) {
      macros_.UndefineAll();
      // The directive takes no arguments, so anything left on the line is
      // ordinary source text rather than an operand and is passed through.
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
