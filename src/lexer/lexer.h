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
    bool at_end() const;
    SourceLoc make_loc() const;

    // Whitespace / comments
    void skip_whitespace_and_comments();
    void skip_line_comment();
    void skip_block_comment();

    // Token construction helpers
    Token make_token(TokenKind kind, SourceLoc loc) const;
    Token make_op(TokenKind kind, SourceLoc loc, uint32_t start);

    // Primary lexing entry points
    Token lex_identifier();
    Token lex_number();
    Token lex_string_literal();
    Token lex_system_identifier();
    Token lex_escaped_identifier();
    Token lex_operator();

    // Number sub-helpers
    Token lex_unbased_unsized(SourceLoc loc, uint32_t start);
    Token lex_based_number(SourceLoc loc, uint32_t start);
    void lex_real_suffix();

    // Operator sub-helpers
    Token lex_op_tilde(SourceLoc loc, uint32_t start);
    Token lex_op_plus(SourceLoc loc, uint32_t start);
    Token lex_op_minus(SourceLoc loc, uint32_t start);
    Token lex_op_star(SourceLoc loc, uint32_t start);
    Token lex_op_caret(SourceLoc loc, uint32_t start);
    Token lex_op_amp(SourceLoc loc, uint32_t start);
    Token lex_op_pipe(SourceLoc loc, uint32_t start);
    Token lex_op_bang(SourceLoc loc, uint32_t start);
    Token lex_op_eq(SourceLoc loc, uint32_t start);
    Token lex_op_hash(SourceLoc loc, uint32_t start);
    Token lex_op_dot(SourceLoc loc, uint32_t start);
    Token lex_op_colon(SourceLoc loc, uint32_t start);
    Token lex_op_at(SourceLoc loc, uint32_t start);
    Token lex_op_slash(SourceLoc loc, uint32_t start);
    Token lex_op_percent(SourceLoc loc, uint32_t start);
    Token lex_angle_left(SourceLoc loc, uint32_t start);
    Token lex_angle_right(SourceLoc loc, uint32_t start);

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
