#include "lexer/lexer.h"

#include <cctype>
#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/lexical_limits.h"
#include "common/source_loc.h"
#include "lexer/keywords.h"
#include "lexer/token.h"

namespace delta {

namespace {

std::string IdentifierTooLongMessage() {
  return std::format("identifier exceeds maximum length of {} characters",
                     kMaxIdentifierLength);
}

bool IsSystemTfSpelling(std::string_view name) {
  if (name.empty() || name.front() != '$') return false;
  for (char ch : name.substr(1)) {
    bool is_word =
        std::isalnum(static_cast<unsigned char>(ch)) || ch == '_' || ch == '$';
    if (!is_word) return false;
  }
  return true;
}

std::vector<std::string_view> SplitPragmaWords(std::string_view body) {
  std::vector<std::string_view> words;
  size_t i = 0;
  while (i < body.size()) {
    while (i < body.size() &&
           std::isspace(static_cast<unsigned char>(body[i]))) {
      ++i;
    }
    size_t start = i;
    while (i < body.size() &&
           !std::isspace(static_cast<unsigned char>(body[i]))) {
      ++i;
    }
    if (i > start) {
      words.push_back(body.substr(start, i - start));
    }
  }
  return words;
}

bool BuildSimpleFsmStatePragma(const std::vector<std::string_view>& words,
                               SourceLoc loc, Lexer::FsmStatePragma& out) {
  out.loc = loc;
  if (words.size() >= 3 && words[1] == "state_vector") {
    out.form = Lexer::FsmStatePragma::Form::kStateVector;
    out.signal_name = words[2];
    if (words.size() == 3) {
      return true;
    }
    if (words.size() == 5 && words[3] == "enum" &&
        Lexer::IsSimplePragmaIdentifier(words[4])) {
      out.has_enum = true;
      out.enum_name = words[4];
      return true;
    }
    return false;
  }
  if (words.size() == 3 && words[1] == "enum" &&
      Lexer::IsSimplePragmaIdentifier(words[2])) {
    out.form = Lexer::FsmStatePragma::Form::kEnumOnly;
    out.has_enum = true;
    out.enum_name = words[2];
    return true;
  }
  return false;
}

bool ParsePartSelectBound(std::string_view text, int& out) {
  int value = 0;
  for (char c : text) {
    if (!std::isdigit(static_cast<unsigned char>(c))) {
      return false;
    }
    int digit = c - '0';
    if (value > (std::numeric_limits<int>::max() - digit) / 10) {
      return false;
    }
    value = value * 10 + digit;
  }
  out = value;
  return true;
}

size_t FindConcatCloseBrace(const std::vector<std::string_view>& words) {
  for (size_t k = 2; k < words.size(); ++k) {
    if (words[k].find('}') != std::string_view::npos) {
      return k;
    }
  }
  return words.size();
}

std::string_view ExtractBracedInside(const std::vector<std::string_view>& words,
                                     size_t close) {
  const char* region_begin = words[2].data();
  const char* region_end = words[close].data() + words[close].size();
  std::string_view region(region_begin,
                          static_cast<size_t>(region_end - region_begin));
  size_t close_brace = region.rfind('}');
  return region.substr(1, close_brace - 1);
}

bool ParseConcatMembers(std::string_view inside,
                        std::vector<std::string_view>& names) {
  size_t i = 0;
  while (true) {
    size_t comma = inside.find(',', i);
    std::string_view piece = comma == std::string_view::npos
                                 ? inside.substr(i)
                                 : inside.substr(i, comma - i);
    size_t b = 0;
    size_t e = piece.size();
    while (b < e && std::isspace(static_cast<unsigned char>(piece[b]))) {
      ++b;
    }
    while (e > b && std::isspace(static_cast<unsigned char>(piece[e - 1]))) {
      --e;
    }
    std::string_view member = piece.substr(b, e - b);
    if (!Lexer::IsSimplePragmaIdentifier(member)) {
      return false;
    }
    names.push_back(member);
    if (comma == std::string_view::npos) {
      break;
    }
    i = comma + 1;
  }
  return !names.empty();
}

bool IsEscapeDigit(char c, bool hex) {
  if (hex) return std::isxdigit(static_cast<unsigned char>(c)) != 0;
  return c >= '0' && c <= '7';
}

}  // namespace

Lexer::Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag,
             TextOrigin origin)
    : source_(source), file_id_(file_id), diag_(diag), origin_(origin) {}

char Lexer::CharAt(uint32_t p) const {
  return p < source_.size() ? source_[p] : '\0';
}

char Lexer::Current() const { return CharAt(pos_); }

char Lexer::PeekChar() const { return CharAt(pos_ + 1); }

void Lexer::Advance() {
  if (AtEnd()) {
    return;
  }
  if (source_[pos_] == '\n') {
    ++line_;
    column_ = 1;
  } else {
    ++column_;
  }
  ++pos_;
}

bool Lexer::AtEnd() const { return pos_ >= source_.size(); }

SourceLoc Lexer::MakeLoc() const { return {file_id_, line_, column_}; }

uint32_t Lexer::SkipLineComment() {
  while (!AtEnd() && Current() != '\n') {
    Advance();
  }
  uint32_t body_end = pos_;
  Advance();
  return body_end;
}

uint32_t Lexer::SkipBlockComment(SourceLoc start_loc) {
  while (!AtEnd()) {
    if (Current() == '*' && PeekChar() == '/') {
      uint32_t body_end = pos_;
      Advance();
      Advance();
      return body_end;
    }
    Advance();
  }
  diag_.Error(start_loc, "unterminated block comment", Subclause("5.4"));
  return pos_;
}

bool Lexer::IsSimplePragmaIdentifier(std::string_view word) {
  if (word.empty()) {
    return false;
  }
  char first = word.front();
  if (!std::isalpha(static_cast<unsigned char>(first)) && first != '_') {
    return false;
  }
  for (char c : word) {
    if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_' && c != '$') {
      return false;
    }
  }
  return true;
}

bool Lexer::ParsePartSelect(std::string_view word, std::string_view& base,
                            int& msb, int& lsb) {
  size_t open = word.find('[');
  if (open == std::string_view::npos || open == 0 || word.back() != ']') {
    return false;
  }
  std::string_view candidate_base = word.substr(0, open);
  if (!IsSimplePragmaIdentifier(candidate_base)) {
    return false;
  }
  std::string_view inside = word.substr(open + 1, word.size() - open - 2);
  size_t colon = inside.find(':');
  if (colon == std::string_view::npos) {
    return false;
  }
  std::string_view hi = inside.substr(0, colon);
  std::string_view lo = inside.substr(colon + 1);
  if (hi.empty() || lo.empty()) {
    return false;
  }
  if (!ParsePartSelectBound(hi, msb) || !ParsePartSelectBound(lo, lsb)) {
    return false;
  }
  base = candidate_base;
  return true;
}

void Lexer::TryRecognizeFsmStatePragma(std::string_view body, SourceLoc loc) {
  auto offset = static_cast<uint32_t>(body.data() - source_.data());
  if (offset < first_unseen_comment_) {
    return;
  }
  first_unseen_comment_ = offset + 1;

  std::vector<std::string_view> words = SplitPragmaWords(body);

  if (words.empty() || words[0] != "tool") {
    return;
  }

  if (words.size() >= 3 && words[1] == "state_vector" &&
      !IsSimplePragmaIdentifier(words[2])) {
    if (words[2].front() == '{') {
      TryRecognizeFsmConcatPragma(words, loc);
    } else {
      TryRecognizeFsmPartSelectPragma(words, loc);
    }
    return;
  }

  FsmStatePragma pragma;
  if (!BuildSimpleFsmStatePragma(words, loc, pragma)) {
    return;
  }
  fsm_state_pragmas_.push_back(pragma);
}

static bool LocBefore(SourceLoc a, SourceLoc b) {
  return a.file_id == b.file_id &&
         (a.line < b.line || (a.line == b.line && a.column < b.column));
}

std::string_view Lexer::ClaimFsmEnumPragma(SourceLoc before) {
  std::string_view claimed;
  while (fsm_pragmas_claimed_ < fsm_state_pragmas_.size()) {
    const FsmStatePragma& pragma = fsm_state_pragmas_[fsm_pragmas_claimed_];
    if (!LocBefore(pragma.loc, before)) break;
    if (pragma.form == FsmStatePragma::Form::kEnumOnly) {
      claimed = pragma.enum_name;
    }
    ++fsm_pragmas_claimed_;
  }
  return claimed;
}

void Lexer::TryRecognizeFsmPartSelectPragma(
    const std::vector<std::string_view>& words, SourceLoc loc) {
  if (words.size() != 6 || words[4] != "enum") {
    return;
  }

  FsmPartSelectPragma pragma;
  if (!ParsePartSelect(words[2], pragma.signal_name, pragma.msb, pragma.lsb)) {
    return;
  }
  if (!IsSimplePragmaIdentifier(words[3]) ||
      !IsSimplePragmaIdentifier(words[5])) {
    return;
  }
  pragma.fsm_name = words[3];
  pragma.enum_name = words[5];
  pragma.loc = loc;
  fsm_part_select_pragmas_.push_back(pragma);
}

void Lexer::ReportConcatSelectProhibition(std::string_view inside,
                                          SourceLoc loc) {
  if (inside.find('[') == std::string_view::npos) {
    return;
  }
  diag_.Warning(loc,
                "bit-select or part-select cannot be used in an FSM "
                "state_vector concatenation",
                Subclause("40.4.3"));
}

void Lexer::TryRecognizeFsmConcatPragma(
    const std::vector<std::string_view>& words, SourceLoc loc) {
  size_t close = FindConcatCloseBrace(words);
  if (close == words.size()) {
    return;
  }
  if (words.size() != close + 4 || words[close + 2] != "enum") {
    return;
  }
  if (!IsSimplePragmaIdentifier(words[close + 1]) ||
      !IsSimplePragmaIdentifier(words[close + 3])) {
    return;
  }

  std::string_view inside = ExtractBracedInside(words, close);

  FsmConcatPragma pragma;
  if (!ParseConcatMembers(inside, pragma.signal_names)) {
    ReportConcatSelectProhibition(inside, loc);
    return;
  }

  pragma.fsm_name = words[close + 1];
  pragma.enum_name = words[close + 3];
  pragma.loc = loc;
  fsm_concat_pragmas_.push_back(pragma);
}

bool Lexer::IsWhiteSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f';
}

void Lexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {
    if (IsWhiteSpace(Current())) {
      Advance();
      continue;
    }
    if (Current() == kKeywordMarker &&
        origin_ == TextOrigin::kPreprocessorOutput) {
      ConsumeKeywordMarker();
      continue;
    }

    if (Current() == '/' && PeekChar() == '/') {
      auto comment_loc = MakeLoc();
      Advance();
      Advance();
      uint32_t body_start = pos_;
      uint32_t body_end = SkipLineComment();
      TryRecognizeFsmStatePragma(
          source_.substr(body_start, body_end - body_start), comment_loc);
      continue;
    }
    if (Current() == '/' && PeekChar() == '*') {
      auto comment_loc = MakeLoc();
      Advance();
      Advance();
      uint32_t body_start = pos_;
      uint32_t body_end = SkipBlockComment(comment_loc);
      TryRecognizeFsmStatePragma(
          source_.substr(body_start, body_end - body_start), comment_loc);
      continue;
    }
    break;
  }
}

bool Lexer::SkipSpacesAndTabs() {
  uint32_t before = pos_;
  while (Current() == ' ' || Current() == '\t') {
    Advance();
  }
  return pos_ != before;
}

void Lexer::ConsumeKeywordMarker() {
  Advance();
  keyword_version_ = static_cast<KeywordVersion>(Current());
  Advance();
}

Token Lexer::MakeToken(TokenKind kind, SourceLoc loc) const {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  return tok;
}

Token Lexer::MakeOp(TokenKind kind, SourceLoc loc, uint32_t start) {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::Next() {
  if (has_peeked_) {
    has_peeked_ = false;
    taken_ = peeked_;
  } else {
    taken_ = Scan();
  }
  return taken_;
}

SourceLoc Lexer::TakenEnd() const {
  SourceLoc end = taken_.loc;
  if (!taken_.text.empty()) {
    end.column += static_cast<uint32_t>(taken_.text.size()) - 1;
  }
  return end;
}

Token Lexer::Scan() {
  SkipWhitespaceAndComments();
  if (AtEnd()) {
    return MakeToken(TokenKind::kEof, MakeLoc());
  }
  char c = Current();
  if (c == '$') {
    char next = PeekChar();
    if (std::isalnum(static_cast<unsigned char>(next)) || next == '_' ||
        next == '$') {
      return LexSystemIdentifier();
    }
    auto loc = MakeLoc();
    uint32_t start = pos_;
    Advance();
    return MakeOp(TokenKind::kDollar, loc, start);
  }
  if (c == '\\') {
    return LexEscapedIdentifier();
  }
  if (c == '"') {
    return LexStringLiteral();
  }
  if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
    return LexIdentifier();
  }
  if (std::isdigit(static_cast<unsigned char>(c))) {
    return LexNumber();
  }
  if (c == '\'') {
    return LexApostrophe();
  }
  return LexOperator();
}

Token Lexer::Peek() {
  if (!has_peeked_) {
    peeked_ = Scan();
    has_peeked_ = true;
  }
  return peeked_;
}

Token Lexer::NextFilePathSpec() {
  has_peeked_ = false;
  SkipWhitespaceAndComments();
  if (AtEnd()) return MakeToken(TokenKind::kEof, MakeLoc());
  auto loc = MakeLoc();
  uint32_t start = pos_;
  while (!AtEnd()) {
    char c = Current();
    if (IsWhiteSpace(c) || c == ',' || c == ';') {
      break;
    }
    Advance();
  }
  if (pos_ == start) {
    diag_.Error(loc, "expected file path specification", Subclause("33.3.1"));
    return MakeToken(TokenKind::kEof, loc);
  }
  Token tok;
  tok.kind = TokenKind::kStringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  while (std::isalnum(static_cast<unsigned char>(Current())) ||
         Current() == '_' || Current() == '$') {
    Advance();
  }
  std::string_view text = source_.substr(start, pos_ - start);
  auto kw = LookupKeyword(text, keyword_version_);
  Token tok;
  tok.kind = kw.value_or(TokenKind::kIdentifier);
  tok.loc = loc;
  tok.text = text;
  if (text.size() > kMaxIdentifierLength) {
    diag_.Error(loc, IdentifierTooLongMessage(), Subclause("5.6"));
  }
  return tok;
}

Token Lexer::LexStringLiteral() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  bool triple = PeekChar() == '"' && CharAt(pos_ + 2) == '"';
  if (triple) {
    Advance();
    Advance();
    Advance();
    if (!LexTripleQuotedBody()) {
      diag_.Error(loc, "unterminated triple-quoted string", Subclause("5.9"));
    }
  } else {
    Advance();
    if (!LexQuotedBody()) {
      diag_.Error(loc, "unterminated string literal", Subclause("5.9"));
    }
  }
  Token tok;
  tok.kind = TokenKind::kStringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::CheckEscapeDigits() {
  uint32_t p = pos_ + 1;
  const bool kHex = CharAt(p) == 'x';
  if (kHex) {
    ++p;
  } else if (!IsEscapeDigit(CharAt(p), false)) {
    return;
  }
  const uint32_t kMax = kHex ? 2 : 3;
  uint32_t taken = 0;
  while (taken < kMax && IsEscapeDigit(CharAt(p), kHex)) {
    ++p;
    ++taken;
  }
  if (taken == kMax) return;
  const char kNext = CharAt(p);
  if (kNext != 'x' && kNext != 'X' && kNext != 'z' && kNext != 'Z' &&
      kNext != '?')
    return;
  diag_.Error(MakeLoc(),
              kHex ? "x or z digit in a hex escape of a string literal"
                   : "x or z digit in an octal escape of a string literal",
              Subclause("5.9.1"));
}

bool Lexer::LexQuotedBody() {
  while (!AtEnd() && Current() != '"') {
    if (Current() == '\n' || Current() == '\r') {
      return false;
    }
    if (Current() == '\\') {
      CheckEscapeDigits();
      Advance();

      if (AtEnd()) return false;
    }
    Advance();
  }
  if (AtEnd()) return false;
  Advance();
  return true;
}

bool Lexer::LexTripleQuotedBody() {
  while (!AtEnd()) {
    if (Current() == '"' && PeekChar() == '"' && CharAt(pos_ + 2) == '"') {
      Advance();
      Advance();
      Advance();
      return true;
    }
    if (Current() == '\\') {
      CheckEscapeDigits();
      Advance();
    }
    Advance();
  }
  return false;
}

Token Lexer::LexSystemIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  Advance();
  while (!AtEnd()) {
    char ch = Current();
    bool is_word =
        std::isalnum(static_cast<unsigned char>(ch)) || ch == '_' || ch == '$';
    if (!is_word) break;
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kSystemIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexEscapedIdentifier() {
  auto loc = MakeLoc();
  Advance();
  uint32_t start = pos_;
  while (!AtEnd()) {
    if (IsWhiteSpace(Current())) break;
    auto c = static_cast<unsigned char>(Current());

    if (c < 33 || c > 126) {
      diag_.Error(MakeLoc(),
                  "escaped identifier contains non-printable character",
                  Subclause("5.6.1"));
    }
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kEscapedIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  if (tok.text.find('.') != std::string_view::npos) {
    dotted_escaped_names_.insert(tok.text);
  }
  if (tok.text.size() > kMaxIdentifierLength) {
    diag_.Error(loc, IdentifierTooLongMessage(), Subclause("5.6"));
  }
  if (IsSystemTfSpelling(tok.text)) {
    diag_.Error(loc,
                std::format("system task or function name '{}' cannot be "
                            "written as an escaped identifier",
                            tok.text),
                Subclause("5.6.3"));
  }
  return tok;
}

std::vector<Token> Lexer::LexAll() {
  std::vector<Token> tokens;
  while (true) {
    auto tok = Next();
    tokens.push_back(tok);
    if (tok.IsEof()) {
      break;
    }
  }
  return tokens;
}

Lexer::SavedPos Lexer::SavePos() const {
  return {pos_,          line_,   column_,          has_peeked_,
          in_attribute_, peeked_, keyword_version_, fsm_pragmas_claimed_};
}

void Lexer::RestorePos(const SavedPos& saved) {
  pos_ = saved.pos;
  line_ = saved.line;
  column_ = saved.column;
  has_peeked_ = saved.has_peeked;
  in_attribute_ = saved.in_attribute;
  peeked_ = saved.peeked;
  keyword_version_ = saved.keyword_version;
  fsm_pragmas_claimed_ = saved.fsm_pragmas_claimed;
}

}  // namespace delta
