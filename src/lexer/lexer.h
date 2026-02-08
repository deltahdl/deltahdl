#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"

#include <string_view>
#include <vector>

namespace delta {

class Lexer {
  public:
    Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag);

    Token next();
    Token peek();

    std::vector<Token> lex_all();

  private:
    char current() const;
    char peek_char() const;
    char peek_char2() const;
    void advance();
    void skip_whitespace_and_comments();
    bool at_end() const;
    SourceLoc make_loc() const;

    Token lex_identifier();
    Token lex_number();
    Token lex_string_literal();
    Token lex_system_identifier();
    Token lex_escaped_identifier();
    Token lex_operator();

    Token lex_angle_left(SourceLoc loc, uint32_t start);
    Token lex_angle_right(SourceLoc loc, uint32_t start);
    Token make_token(TokenKind kind, SourceLoc loc) const;

    std::string_view source_;
    uint32_t pos_ = 0;
    uint32_t line_ = 1;
    uint32_t column_ = 1;
    uint32_t file_id_;
    DiagEngine& diag_;
    bool has_peeked_ = false;
    Token peeked_;
};

} // namespace delta
