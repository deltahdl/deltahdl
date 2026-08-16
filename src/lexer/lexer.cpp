#include "lexer/lexer.h"

#include <cctype>

#include "lexer/keywords.h"

namespace delta {

namespace {

// Split a pragma comment body into whitespace-delimited words.
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

// Build the simple §40.4.1 current-state / enum-only pragma from a word list
// whose leading `tool` keyword the caller has already matched. Returns true and
// fills `out` for a recognized simple form, false otherwise. A `state_vector`
// word whose state operand is not a simple identifier is a descendant form
// (§40.4.2 / §40.4.3); the caller handles that case before calling this.
bool BuildSimpleFsmStatePragma(const std::vector<std::string_view>& words,
                               SourceLoc loc, Lexer::FsmStatePragma& out) {
  out.loc = loc;
  if (words.size() >= 3 && words[1] == "state_vector") {
    out.form = Lexer::FsmStatePragma::Form::kStateVector;
    out.signal_name = words[2];
    if (words.size() == 3) {
      // Bare current-state pragma; the enum name is supplied separately.
      return true;
    }
    if (words.size() == 5 && words[3] == "enum" &&
        Lexer::IsSimplePragmaIdentifier(words[4])) {
      out.has_enum = true;
      out.enum_name = words[4];
      return true;
    }
    // An interposed FSM name or other trailing tokens belong to the descendant
    // pragma forms, not the simple §40.4.1 signal pragma.
    return false;
  }
  if (words.size() == 3 && words[1] == "enum" &&
      Lexer::IsSimplePragmaIdentifier(words[2])) {
    // Separate `tool enum enumeration_name` pragma placed after the bit range.
    out.form = Lexer::FsmStatePragma::Form::kEnumOnly;
    out.has_enum = true;
    out.enum_name = words[2];
    return true;
  }
  return false;
}

// Find the index of the word carrying the closing brace of a §40.4.3
// concatenation. The braced list may span several whitespace-delimited words.
// Returns words.size() when no closing brace is present.
size_t FindConcatCloseBrace(const std::vector<std::string_view>& words) {
  for (size_t k = 2; k < words.size(); ++k) {
    if (words[k].find('}') != std::string_view::npos) {
      return k;
    }
  }
  return words.size();
}

// Reconstruct the `{...}` region as one contiguous view of the source, so the
// internal spaces and commas are preserved regardless of how the comment body
// split into words, and return the text between the braces. Returns true and
// fills `inside` on success.
bool ExtractBracedInside(const std::vector<std::string_view>& words,
                         size_t close, std::string_view& inside) {
  const char* region_begin = words[2].data();
  const char* region_end = words[close].data() + words[close].size();
  std::string_view region(region_begin,
                          static_cast<size_t>(region_end - region_begin));
  size_t open_brace = region.find('{');
  size_t close_brace = region.rfind('}');
  if (open_brace == std::string_view::npos ||
      close_brace == std::string_view::npos || close_brace <= open_brace) {
    return false;
  }
  inside = region.substr(open_brace + 1, close_brace - open_brace - 1);
  return true;
}

// Split a concatenation body on commas and collect every member. Each member
// must be a whole signal: §40.4.3 forbids bit-selects or part-selects here,
// which IsSimplePragmaIdentifier rejects (a `[` is not an identifier
// character). Returns true and fills `names` when every member is valid.
bool ParseConcatMembers(std::string_view inside,
                        std::vector<std::string_view>& names) {
  size_t i = 0;
  while (i <= inside.size()) {
    size_t comma = inside.find(',', i);
    std::string_view piece = comma == std::string_view::npos
                                 ? inside.substr(i)
                                 : inside.substr(i, comma - i);
    // Trim surrounding whitespace from the member.
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

// Returns true if a pragma carrying this exact source location was already
// recorded, so the lexer does not double-record a comment it backtracks over.
template <typename PragmaVec>
bool PragmaAlreadyRecorded(const PragmaVec& recorded, SourceLoc loc) {
  for (const auto& existing : recorded) {
    if (existing.loc.file_id == loc.file_id && existing.loc.line == loc.line &&
        existing.loc.column == loc.column) {
      return true;
    }
  }
  return false;
}

}  // namespace

// Decide whether the apostrophe at `apostrophe_pos` opens a based integer
// literal. §5.7.1 makes the size constant optional, so both callers ask this:
// Lexer::LexNumber of the apostrophe that follows a size, as in 8'h99, and
// Lexer::LexApostrophe of an apostrophe written without one, as in 'h99. The
// grammar requires an optional s/S signed marker and then one of the base
// letters d/D/b/B/o/O/h/H. Anything else — most importantly a left
// parenthesis or left brace — keeps the apostrophe a separate token so that
// the '(expr) and '{...} cast and assignment-pattern forms tokenize
// correctly.
//
// Spaces and tabs standing before the signed marker or before the base letter
// are read past, so that `8' h99` and `' h99` reach Lexer::LexBasedNumber and
// are reported there against the §5.7.1 sentence forbidding white space
// between the apostrophe and the base format character. What follows the white
// space still has to be a base letter, so the answer stays false for `'(x)`
// and `4' (x)`, for `'{...}` and `4' {...}`, and for the unsized single-bit
// forms '0, '1, 'x and 'z.
bool Lexer::ApostropheStartsBaseSpecifier(uint32_t apostrophe_pos) const {
  auto skip_spaces_and_tabs = [this](uint32_t p) {
    while (p < source_.size() && (source_[p] == ' ' || source_[p] == '\t')) {
      ++p;
    }
    return p;
  };
  uint32_t look = skip_spaces_and_tabs(apostrophe_pos + 1);
  if (look < source_.size() && (source_[look] == 's' || source_[look] == 'S')) {
    look = skip_spaces_and_tabs(look + 1);
  }
  char base = (look < source_.size()) ? source_[look] : '\0';
  return base == 'd' || base == 'D' || base == 'b' || base == 'B' ||
         base == 'o' || base == 'O' || base == 'h' || base == 'H';
}

Lexer::Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag)
    : source_(source), file_id_(file_id), diag_(diag) {}

char Lexer::Current() const {
  if (AtEnd()) {
    return '\0';
  }
  return source_[pos_];
}

char Lexer::PeekChar() const {
  if (pos_ + 1 >= source_.size()) {
    return '\0';
  }
  return source_[pos_ + 1];
}

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
  if (!AtEnd() && Current() == '\n') {
    Advance();
  }
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
    if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_') {
      return false;
    }
  }
  return true;
}

bool Lexer::ParsePartSelect(std::string_view word, std::string_view& base,
                            int& msb, int& lsb) {
  // A §40.4.2 part-select word has the shape `signal_name[msb:lsb]`: a simple
  // base identifier followed by a bracketed two-bound range.
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
  auto parse_index = [](std::string_view text, int& out) -> bool {
    int value = 0;
    for (char c : text) {
      if (!std::isdigit(static_cast<unsigned char>(c))) {
        return false;
      }
      value = value * 10 + (c - '0');
    }
    out = value;
    return true;
  };
  if (!parse_index(hi, msb) || !parse_index(lo, lsb)) {
    return false;
  }
  base = candidate_base;
  return true;
}

void Lexer::TryRecognizeFsmStatePragma(std::string_view body, SourceLoc loc) {
  // Split the comment body into whitespace-delimited words.
  std::vector<std::string_view> words = SplitPragmaWords(body);

  // Every §40.4.1 FSM pragma opens with the required `tool` keyword.
  if (words.empty() || words[0] != "tool") {
    return;
  }

  // A `state_vector` word whose state operand is not a simple identifier is a
  // descendant form (§40.4.2 part-select / §40.4.3 concatenation), not the
  // simple signal named by §40.4.1; dispatch to the matching recognizer.
  if (words.size() >= 3 && words[1] == "state_vector" &&
      !IsSimplePragmaIdentifier(words[2])) {
    if (!words[2].empty() && words[2].front() == '{') {
      // §40.4.3: a concatenation of signals can hold the current state. The
      // pragma supplies an FSM name and an enumeration name:
      //   `tool state_vector {sig , sig, ...} FSM_name enum enum_name`.
      TryRecognizeFsmConcatPragma(words, loc);
    } else {
      // §40.4.2: a part-select of a vector signal can hold the current state.
      // Such a pragma must also supply an FSM name for the coverage tool to
      // report under, distinct from the enumeration name:
      //   `tool state_vector signal_name[msb:lsb] FSM_name enum enum_name`.
      TryRecognizeFsmPartSelectPragma(words, loc);
    }
    return;
  }

  FsmStatePragma pragma;
  if (!BuildSimpleFsmStatePragma(words, loc, pragma)) {
    return;
  }

  // Avoid re-recording the same comment if the lexer backtracks over it.
  if (PragmaAlreadyRecorded(fsm_state_pragmas_, loc)) {
    return;
  }
  fsm_state_pragmas_.push_back(pragma);
}

void Lexer::TryRecognizeFsmPartSelectPragma(
    const std::vector<std::string_view>& words, SourceLoc loc) {
  // The caller has already matched the leading `tool state_vector`. §40.4.2's
  // form names a part-select, an FSM name, and an enumeration name:
  //   tool state_vector signal_name[msb:lsb] FSM_name enum enum_name
  if (words.size() != 6 || words[4] != "enum") {
    return;
  }

  FsmPartSelectPragma pragma;
  if (!ParsePartSelect(words[2], pragma.signal_name, pragma.msb, pragma.lsb)) {
    return;
  }
  // The FSM name is required so the coverage tool has a name to report the FSM
  // under, and it is distinct from the enumeration name.
  if (!IsSimplePragmaIdentifier(words[3]) ||
      !IsSimplePragmaIdentifier(words[5])) {
    return;
  }
  pragma.fsm_name = words[3];
  pragma.enum_name = words[5];
  pragma.loc = loc;

  // Avoid re-recording the same comment if the lexer backtracks over it.
  if (PragmaAlreadyRecorded(fsm_part_select_pragmas_, loc)) {
    return;
  }
  fsm_part_select_pragmas_.push_back(pragma);
}

void Lexer::TryRecognizeFsmConcatPragma(
    const std::vector<std::string_view>& words, SourceLoc loc) {
  // The caller has already matched the leading `tool state_vector`. §40.4.3's
  // form names a brace-delimited concatenation, an FSM name, and an enumeration
  // name:  tool state_vector { sig , sig, ... } FSM_name enum enum_name
  // The braced list may be split across several whitespace-delimited words, so
  // find the word carrying the closing brace and rejoin the brace region from
  // the contiguous source span the words point into.
  if (words.size() < 3 || words[2].empty() || words[2].front() != '{') {
    return;
  }
  size_t close = FindConcatCloseBrace(words);
  if (close == words.size()) {
    return;  // no closing brace for the concatenation
  }
  // The braced list is followed by exactly three words: the FSM name, the
  // literal `enum` keyword, and the enumeration name.
  if (words.size() != close + 4 || words[close + 2] != "enum") {
    return;
  }
  if (!IsSimplePragmaIdentifier(words[close + 1]) ||
      !IsSimplePragmaIdentifier(words[close + 3])) {
    return;
  }

  std::string_view inside;
  if (!ExtractBracedInside(words, close, inside)) {
    return;
  }

  FsmConcatPragma pragma;
  if (!ParseConcatMembers(inside, pragma.signal_names)) {
    return;
  }

  pragma.fsm_name = words[close + 1];
  pragma.enum_name = words[close + 3];
  pragma.loc = loc;

  // Avoid re-recording the same comment if the lexer backtracks over it.
  if (PragmaAlreadyRecorded(fsm_concat_pragmas_, loc)) {
    return;
  }
  fsm_concat_pragmas_.push_back(pragma);
}

void Lexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {
    if (std::isspace(static_cast<unsigned char>(Current()))) {
      Advance();
      continue;
    }
    if (Current() == kKeywordMarker) {
      ConsumeKeywordMarker();
      continue;
    }

    if (Current() == '/' && PeekChar() == '/') {
      // §40.4.7 — the FSM recognition pragmas work in one-line comments that
      // follow `//` just as they do in `/* */` block comments. Skip the comment
      // and hand its body to the same recognizer the block-comment path uses.
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

// Consume the run of spaces and tabs at the current position and report
// whether there was one. Callers that must know whether white space stood at a
// point in the source read the result; callers that only need to step over it
// discard it.
bool Lexer::SkipSpacesAndTabs() {
  uint32_t before = pos_;
  while (!AtEnd() && (Current() == ' ' || Current() == '\t')) {
    Advance();
  }
  return pos_ != before;
}

void Lexer::ConsumeKeywordMarker() {
  Advance();
  if (!AtEnd()) {
    keyword_version_ = static_cast<KeywordVersion>(Current());
    Advance();
  }
  if (!AtEnd() && Current() == '\n') {
    Advance();
  }
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
    return peeked_;
  }
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
    peeked_ = Next();
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
    if (std::isspace(static_cast<unsigned char>(c)) || c == ',' || c == ';') {
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
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_' || Current() == '$')) {
    Advance();
  }
  std::string_view text = source_.substr(start, pos_ - start);
  auto kw = LookupKeyword(text, keyword_version_);
  Token tok;
  tok.kind = kw.value_or(TokenKind::kIdentifier);
  tok.loc = loc;
  tok.text = text;
  if (text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters",
                Subclause("5.6"));
  }
  return tok;
}

Token Lexer::LexUnbasedUnsized(SourceLoc loc, uint32_t start) {
  Advance();
  if (!AtEnd()) {
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kUnbasedUnsizedLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::ValidateDecimalXZ(SourceLoc loc, char base_letter,
                              uint32_t digit_start) {
  if (base_letter != 'd' && base_letter != 'D') return;

  uint32_t digit_count = 0;
  bool has_xz = false;
  for (uint32_t i = digit_start; i < pos_; ++i) {
    char c = source_[i];
    if (c == '_') continue;
    ++digit_count;
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') {
      has_xz = true;
    }
  }
  if (has_xz && digit_count > 1) {
    diag_.Error(loc, "x, z, or ? in decimal literal must be the only digit",
                Subclause("5.7.1"));
  }
}

void Lexer::ValidateBaseDigits(SourceLoc loc, char base_letter,
                               uint32_t digit_start) {
  for (uint32_t i = digit_start; i < pos_; ++i) {
    char c = source_[i];
    if (c == '_' || c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?')
      continue;
    bool valid = false;
    switch (base_letter) {
      case 'b':
      case 'B':
        valid = (c == '0' || c == '1');
        break;
      case 'o':
      case 'O':
        valid = (c >= '0' && c <= '7');
        break;
      case 'd':
      case 'D':
        valid = (c >= '0' && c <= '9');
        break;
      case 'h':
      case 'H':
        valid = std::isxdigit(static_cast<unsigned char>(c));
        break;
      default:
        break;
    }
    if (!valid) {
      diag_.Error(loc, "illegal digit for specified base", Subclause("5.7.1"));
      return;
    }
  }
}

Token Lexer::LexBasedNumber(SourceLoc loc, uint32_t start) {
  Advance();

  // §5.7.1: "The apostrophe character and the base format character shall not
  // be separated by any white space." The optional s/S signed marker stands
  // between them, so white space is forbidden on either side of it. Read the
  // literal as it was written whatever the answer, so that one token still
  // spans it, and report the sentence once even when both places carry white
  // space.
  bool space_before_sign = SkipSpacesAndTabs();
  if (!AtEnd() && (Current() == 's' || Current() == 'S')) {
    Advance();
  }
  bool space_before_base = SkipSpacesAndTabs();
  if (space_before_sign || space_before_base) {
    diag_.Error(loc,
                "white space shall not separate the apostrophe from the base "
                "format character",
                Subclause("5.7.1"));
  }
  char base_letter = '\0';
  if (!AtEnd()) {
    base_letter = Current();
    Advance();
  }

  // §5.7.1: "The unsigned number token shall immediately follow the base
  // format, optionally preceded by white space." This white space is legal, so
  // stepping over it draws no report.
  SkipSpacesAndTabs();
  uint32_t before_digits = pos_;
  // §5.7.1: "The third token, an unsigned number, shall consist of digits that
  // are legal for the specified base format." A letter or digit that is illegal
  // for the base is still written where the value token belongs, so the run
  // covers every alphanumeric character and Lexer::ValidateBaseDigits judges
  // what it collected against the base. Ending the run at the first character
  // no base accepts would hand that function a span it can never reject for a
  // hexadecimal literal, and would leave `4'hG` reported as a literal carrying
  // no value at all.
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_' || Current() == '?')) {
    Advance();
  }
  if (pos_ == before_digits) {
    if (!AtEnd() && (Current() == '+' || Current() == '-')) {
      // §5.7.1: "A plus or minus operator between the base format and the
      // number is an illegal syntax", which Example 3 writes as `8 'd -6`. The
      // sign is no part of the value token, so a literal written with one
      // arrives here with an empty value run, and the character that stopped
      // the run is what says which sentence the source broke.
      diag_.Error(loc,
                  "plus or minus operator between the base format and the "
                  "number is illegal syntax",
                  Subclause("5.7.1"));
    } else {
      diag_.Error(loc, "missing value digits after base specifier",
                  Subclause("5.7.1"));
    }
  }
  if (pos_ > before_digits && source_[before_digits] == '_') {
    diag_.Error(loc, "underscore cannot be first character of number value",
                Subclause("5.7.1"));
  }
  ValidateBaseDigits(loc, base_letter, before_digits);
  ValidateDecimalXZ(loc, base_letter, before_digits);
  Token tok;
  tok.kind = TokenKind::kIntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::LexFractionalPart() {
  if (AtEnd() || Current() != '.') return;
  if (!std::isdigit(static_cast<unsigned char>(PeekChar()))) return;
  Advance();
  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }
}

void Lexer::LexExponentPart() {
  if (AtEnd()) return;
  if (Current() != 'e' && Current() != 'E') return;

  uint32_t look = pos_ + 1;
  if (look < source_.size() && (source_[look] == '+' || source_[look] == '-')) {
    ++look;
  }
  if (look >= source_.size() ||
      !std::isdigit(static_cast<unsigned char>(source_[look]))) {
    return;
  }
  Advance();
  if (!AtEnd() && (Current() == '+' || Current() == '-')) {
    Advance();
  }
  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }
}

bool Lexer::IsWordBoundary(uint32_t p) const {
  return p >= source_.size() ||
         (!std::isalnum(source_[p]) && source_[p] != '_');
}

bool Lexer::TryLexTimeSuffix() {
  if (AtEnd()) return false;
  uint32_t save = pos_;

  if (pos_ + 1 < source_.size()) {
    char c0 = source_[pos_];
    char c1 = source_[pos_ + 1];
    bool is_two_char =
        (c0 == 'm' || c0 == 'u' || c0 == 'n' || c0 == 'p' || c0 == 'f') &&
        c1 == 's';
    if (is_two_char && IsWordBoundary(pos_ + 2)) {
      Advance();
      Advance();
      return true;
    }
  }

  if (source_[pos_] == 's' && IsWordBoundary(pos_ + 1)) {
    Advance();
    return true;
  }
  pos_ = save;
  return false;
}

Token Lexer::LexNumber() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  if (Current() == '\'') {
    return LexUnbasedUnsized(loc, start);
  }

  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }

  // §5.7.1 permits white space between the size and the apostrophe, as
  // Example 2's `5 'D 3` writes it, so reading past white space is the only way
  // to learn whether this number ends here or carries a base specifier. Both
  // counters are put back when it does not: Advance() moved column_ over the
  // white space, SkipWhitespaceAndComments() moves it over the same characters
  // again before the next token, and a column counted twice locates that token
  // and every later one on the line past where it is written.
  uint32_t before_ws = pos_;
  uint32_t column_before_ws = column_;
  SkipSpacesAndTabs();

  if (!AtEnd() && Current() == '\'' && ApostropheStartsBaseSpecifier(pos_)) {
    return LexBasedNumber(loc, start);
  }
  pos_ = before_ws;
  column_ = column_before_ws;

  uint32_t before_real = pos_;
  LexFractionalPart();
  uint32_t before_exp = pos_;
  LexExponentPart();
  bool has_exponent = (pos_ != before_exp);
  bool is_real = (pos_ != before_real);

  bool is_time = !has_exponent && TryLexTimeSuffix();

  Token tok;
  tok.kind = is_time   ? TokenKind::kTimeLiteral
             : is_real ? TokenKind::kRealLiteral
                       : TokenKind::kIntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexStringLiteral() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  bool triple = PeekChar() == '"' && pos_ + 2 < source_.size() &&
                source_[pos_ + 2] == '"';
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

bool Lexer::LexQuotedBody() {
  while (!AtEnd() && Current() != '"') {
    if (Current() == '\n' || Current() == '\r') {
      return false;
    }
    if (Current() == '\\') {
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
    if (Current() == '"' && PeekChar() == '"' && pos_ + 2 < source_.size() &&
        source_[pos_ + 2] == '"') {
      Advance();
      Advance();
      Advance();
      return true;
    }
    if (Current() == '\\') {
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
  if (tok.text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters",
                Subclause("5.6"));
  }
  return tok;
}

Token Lexer::LexEscapedIdentifier() {
  auto loc = MakeLoc();
  Advance();
  uint32_t start = pos_;
  while (!AtEnd()) {
    auto c = static_cast<unsigned char>(Current());
    if (std::isspace(c)) {
      break;
    }

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
  if (tok.text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters",
                Subclause("5.6"));
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
  return {pos_,          line_,   column_,         has_peeked_,
          in_attribute_, peeked_, keyword_version_};
}

void Lexer::RestorePos(const SavedPos& saved) {
  pos_ = saved.pos;
  line_ = saved.line;
  column_ = saved.column;
  has_peeked_ = saved.has_peeked;
  in_attribute_ = saved.in_attribute;
  peeked_ = saved.peeked;
  keyword_version_ = saved.keyword_version;
}

}  // namespace delta
