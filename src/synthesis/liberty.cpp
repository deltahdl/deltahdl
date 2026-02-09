#include "synthesis/liberty.h"

#include <cctype>
#include <cstdlib>
#include <string>
#include <string_view>
#include <vector>

namespace delta {
namespace {

// =============================================================================
// Token types
// =============================================================================

enum class TokKind : uint8_t {
  kIdent,
  kString,
  kNumber,
  kLParen,
  kRParen,
  kLBrace,
  kRBrace,
  kColon,
  kSemicolon,
  kEof,
};

struct Token {
  TokKind kind = TokKind::kEof;
  std::string text;
};

// =============================================================================
// Tokenizer
// =============================================================================

class Tokenizer {
 public:
  explicit Tokenizer(std::string_view src) : src_(src) {}

  Token Next() {
    SkipWhitespaceAndComments();
    if (pos_ >= src_.size()) return {TokKind::kEof, ""};
    char ch = src_[pos_];
    if (ch == '(') return SingleChar(TokKind::kLParen);
    if (ch == ')') return SingleChar(TokKind::kRParen);
    if (ch == '{') return SingleChar(TokKind::kLBrace);
    if (ch == '}') return SingleChar(TokKind::kRBrace);
    if (ch == ':') return SingleChar(TokKind::kColon);
    if (ch == ';') return SingleChar(TokKind::kSemicolon);
    if (ch == '"') return ReadString();
    if (std::isdigit(ch) || ch == '-' || ch == '.') return ReadNumber();
    return ReadIdent();
  }

 private:
  void SkipWhitespaceAndComments() {
    while (pos_ < src_.size()) {
      if (std::isspace(src_[pos_])) {
        ++pos_;
        continue;
      }
      if (pos_ + 1 < src_.size() && src_[pos_] == '/' &&
          src_[pos_ + 1] == '*') {
        SkipBlockComment();
        continue;
      }
      break;
    }
  }

  void SkipBlockComment() {
    pos_ += 2;  // skip /*
    while (pos_ + 1 < src_.size()) {
      if (src_[pos_] == '*' && src_[pos_ + 1] == '/') {
        pos_ += 2;
        return;
      }
      ++pos_;
    }
    pos_ = src_.size();
  }

  Token SingleChar(TokKind kind) {
    Token tok{kind, std::string(1, src_[pos_])};
    ++pos_;
    return tok;
  }

  Token ReadString() {
    ++pos_;  // skip opening quote
    std::string text;
    while (pos_ < src_.size() && src_[pos_] != '"') {
      text += src_[pos_++];
    }
    if (pos_ < src_.size()) ++pos_;  // skip closing quote
    return {TokKind::kString, std::move(text)};
  }

  Token ReadNumber() {
    size_t start = pos_;
    if (src_[pos_] == '-') ++pos_;
    while (pos_ < src_.size() &&
           (std::isdigit(src_[pos_]) || src_[pos_] == '.'))
      ++pos_;
    // Handle exponent notation (e.g., 1.5e-3).
    if (pos_ < src_.size() && (src_[pos_] == 'e' || src_[pos_] == 'E')) {
      ++pos_;
      if (pos_ < src_.size() && (src_[pos_] == '+' || src_[pos_] == '-'))
        ++pos_;
      while (pos_ < src_.size() && std::isdigit(src_[pos_])) ++pos_;
    }
    return {TokKind::kNumber, std::string(src_.substr(start, pos_ - start))};
  }

  Token ReadIdent() {
    size_t start = pos_;
    while (pos_ < src_.size() &&
           (std::isalnum(src_[pos_]) || src_[pos_] == '_'))
      ++pos_;
    return {TokKind::kIdent, std::string(src_.substr(start, pos_ - start))};
  }

  std::string_view src_;
  size_t pos_ = 0;
};

// =============================================================================
// Parser
// =============================================================================

class LibertyParser {
 public:
  explicit LibertyParser(std::string_view src) : tok_(src) { Advance(); }

  Liberty Parse() {
    Liberty lib;
    Expect(TokKind::kIdent, "library");
    Expect(TokKind::kLParen);
    lib.library_name = cur_.text;
    Advance();
    Expect(TokKind::kRParen);
    Expect(TokKind::kLBrace);
    ParseLibraryBody(lib);
    Expect(TokKind::kRBrace);
    return lib;
  }

 private:
  void Advance() { cur_ = tok_.Next(); }

  void Expect(TokKind kind) {
    if (cur_.kind == kind) Advance();
  }

  void Expect(TokKind kind, const std::string& text) {
    if (cur_.kind == kind && cur_.text == text) Advance();
  }

  void ParseLibraryBody(Liberty& lib) {
    while (cur_.kind != TokKind::kRBrace && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kIdent && cur_.text == "cell") {
        lib.cells.push_back(ParseCell());
      } else {
        SkipAttribute();
      }
    }
  }

  LibCell ParseCell() {
    LibCell cell;
    Expect(TokKind::kIdent, "cell");
    Expect(TokKind::kLParen);
    cell.name = cur_.text;
    Advance();
    Expect(TokKind::kRParen);
    Expect(TokKind::kLBrace);
    ParseCellBody(cell);
    Expect(TokKind::kRBrace);
    return cell;
  }

  void ParseCellBody(LibCell& cell) {
    while (cur_.kind != TokKind::kRBrace && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kIdent && cur_.text == "pin") {
        cell.pins.push_back(ParsePin());
      } else if (cur_.kind == TokKind::kIdent && cur_.text == "timing") {
        cell.timing.push_back(ParseTiming());
      } else if (cur_.kind == TokKind::kIdent && cur_.text == "area") {
        cell.area = ParseFloatAttribute();
      } else {
        SkipAttribute();
      }
    }
  }

  LibPin ParsePin() {
    LibPin pin;
    Expect(TokKind::kIdent, "pin");
    Expect(TokKind::kLParen);
    pin.name = cur_.text;
    Advance();
    Expect(TokKind::kRParen);
    Expect(TokKind::kLBrace);
    ParsePinBody(pin);
    Expect(TokKind::kRBrace);
    return pin;
  }

  void ParsePinBody(LibPin& pin) {
    while (cur_.kind != TokKind::kRBrace && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kIdent && cur_.text == "direction") {
        pin.direction = ParseStringAttribute();
      } else if (cur_.kind == TokKind::kIdent && cur_.text == "function") {
        pin.function = ParseQuotedAttribute();
      } else {
        SkipAttribute();
      }
    }
  }

  LibTiming ParseTiming() {
    LibTiming timing;
    Expect(TokKind::kIdent, "timing");
    Expect(TokKind::kLParen);
    Expect(TokKind::kRParen);
    Expect(TokKind::kLBrace);
    ParseTimingBody(timing);
    Expect(TokKind::kRBrace);
    return timing;
  }

  void ParseTimingBody(LibTiming& timing) {
    while (cur_.kind != TokKind::kRBrace && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kIdent && cur_.text == "related_pin") {
        timing.related_pin = ParseQuotedAttribute();
      } else if (cur_.kind == TokKind::kIdent && cur_.text == "cell_rise") {
        timing.cell_rise = ParseFloatAttribute();
      } else if (cur_.kind == TokKind::kIdent && cur_.text == "cell_fall") {
        timing.cell_fall = ParseFloatAttribute();
      } else {
        SkipAttribute();
      }
    }
  }

  // Parse "key : value ;" where value is an unquoted identifier.
  std::string ParseStringAttribute() {
    Advance();  // skip attribute name
    Expect(TokKind::kColon);
    std::string val = cur_.text;
    Advance();
    if (cur_.kind == TokKind::kSemicolon) Advance();
    return val;
  }

  // Parse "key : \"value\" ;" where value is a quoted string.
  std::string ParseQuotedAttribute() {
    Advance();  // skip attribute name
    Expect(TokKind::kColon);
    std::string val = cur_.text;
    Advance();
    if (cur_.kind == TokKind::kSemicolon) Advance();
    return val;
  }

  // Parse "key : number ;" and return float value.
  float ParseFloatAttribute() {
    Advance();  // skip attribute name
    Expect(TokKind::kColon);
    float val = std::strtof(cur_.text.c_str(), nullptr);
    Advance();
    if (cur_.kind == TokKind::kSemicolon) Advance();
    return val;
  }

  // Skip an unrecognized attribute or group.
  void SkipAttribute() {
    Advance();  // skip name
    // Group with parenthesized header.
    if (cur_.kind == TokKind::kLParen) {
      SkipParenthesized();
      if (cur_.kind == TokKind::kLBrace) SkipBraced();
      return;
    }
    // Simple attribute: skip to semicolon or next block.
    if (cur_.kind == TokKind::kColon) {
      Advance();  // skip colon
      SkipToSemicolon();
      return;
    }
  }

  void SkipParenthesized() {
    if (cur_.kind != TokKind::kLParen) return;
    Advance();
    int depth = 1;
    while (depth > 0 && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kLParen) ++depth;
      if (cur_.kind == TokKind::kRParen) --depth;
      Advance();
    }
  }

  void SkipBraced() {
    if (cur_.kind != TokKind::kLBrace) return;
    Advance();
    int depth = 1;
    while (depth > 0 && cur_.kind != TokKind::kEof) {
      if (cur_.kind == TokKind::kLBrace) ++depth;
      if (cur_.kind == TokKind::kRBrace) --depth;
      Advance();
    }
  }

  void SkipToSemicolon() {
    while (cur_.kind != TokKind::kSemicolon && cur_.kind != TokKind::kRBrace &&
           cur_.kind != TokKind::kEof) {
      Advance();
    }
    if (cur_.kind == TokKind::kSemicolon) Advance();
  }

  Tokenizer tok_;
  Token cur_;
};

}  // namespace

// =============================================================================
// Public API
// =============================================================================

Liberty ParseLiberty(std::string_view source) {
  LibertyParser parser(source);
  return parser.Parse();
}

}  // namespace delta
