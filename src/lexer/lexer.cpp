#include "lexer/lexer.h"
#include "lexer/keywords.h"

#include <cctype>

namespace delta {

Lexer::Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag)
    : source_(source), file_id_(file_id), diag_(diag) {}

char Lexer::current() const {
    if (at_end()) {
        return '\0';
    }
    return source_[pos_];
}

char Lexer::peek_char() const {
    if (pos_ + 1 >= source_.size()) {
        return '\0';
    }
    return source_[pos_ + 1];
}

char Lexer::peek_char2() const {
    if (pos_ + 2 >= source_.size()) {
        return '\0';
    }
    return source_[pos_ + 2];
}

void Lexer::advance() {
    if (at_end()) {
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

bool Lexer::at_end() const {
    return pos_ >= source_.size();
}

SourceLoc Lexer::make_loc() const {
    return {file_id_, line_, column_};
}

void Lexer::skip_whitespace_and_comments() {
    while (!at_end()) {
        if (std::isspace(static_cast<unsigned char>(current()))) {
            advance();
            continue;
        }
        if (current() == '/' && peek_char() == '/') {
            while (!at_end() && current() != '\n') {
                advance();
            }
            continue;
        }
        if (current() != '/' || peek_char() != '*') {
            break;
        }
        advance();
        advance();
        while (!at_end()) {
            if (current() == '*' && peek_char() == '/') {
                advance();
                advance();
                break;
            }
            advance();
        }
    }
}

Token Lexer::make_token(TokenKind kind, SourceLoc loc) const {
    Token tok;
    tok.kind = kind;
    tok.loc = loc;
    return tok;
}

Token Lexer::next() {
    if (has_peeked_) {
        has_peeked_ = false;
        return peeked_;
    }
    skip_whitespace_and_comments();
    if (at_end()) {
        return make_token(TokenKind::Eof, make_loc());
    }
    char c = current();
    if (c == '$') {
        return lex_system_identifier();
    }
    if (c == '\\') {
        return lex_escaped_identifier();
    }
    if (c == '"') {
        return lex_string_literal();
    }
    if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
        return lex_identifier();
    }
    if (std::isdigit(static_cast<unsigned char>(c))) {
        return lex_number();
    }
    if (c == '\'' && !std::isalpha(static_cast<unsigned char>(peek_char()))) {
        return lex_number();
    }
    return lex_operator();
}

Token Lexer::peek() {
    if (!has_peeked_) {
        peeked_ = next();
        has_peeked_ = true;
    }
    return peeked_;
}

Token Lexer::lex_identifier() {
    auto loc = make_loc();
    uint32_t start = pos_;
    while (!at_end() && (std::isalnum(static_cast<unsigned char>(current())) || current() == '_' ||
                         current() == '$')) {
        advance();
    }
    std::string_view text = source_.substr(start, pos_ - start);
    auto kw = lookup_keyword(text);
    Token tok;
    tok.kind = kw.value_or(TokenKind::Identifier);
    tok.loc = loc;
    tok.text = text;
    return tok;
}

Token Lexer::lex_number() {
    auto loc = make_loc();
    uint32_t start = pos_;

    // Handle unbased unsized literal: '0, '1, 'x, 'z
    if (current() == '\'') {
        advance();
        if (!at_end()) {
            advance();
        }
        Token tok;
        tok.kind = TokenKind::UnbasedUnsizedLiteral;
        tok.loc = loc;
        tok.text = source_.substr(start, pos_ - start);
        return tok;
    }

    // Decimal digits
    while (!at_end() && (std::isdigit(static_cast<unsigned char>(current())) || current() == '_')) {
        advance();
    }

    // Check for base specifier: 'h, 'b, 'o, 'd
    if (!at_end() && current() == '\'') {
        advance();
        if (!at_end()) {
            advance(); // base letter
        }
        while (!at_end() && (std::isxdigit(static_cast<unsigned char>(current())) ||
                             current() == '_' || current() == 'x' || current() == 'z' ||
                             current() == 'X' || current() == 'Z' || current() == '?')) {
            advance();
        }
        Token tok;
        tok.kind = TokenKind::IntLiteral;
        tok.loc = loc;
        tok.text = source_.substr(start, pos_ - start);
        return tok;
    }

    // Check for real literal (decimal point or exponent)
    if (!at_end() && current() == '.' && std::isdigit(static_cast<unsigned char>(peek_char()))) {
        advance();
        while (!at_end() && (std::isdigit(static_cast<unsigned char>(current())) || current() == '_')) {
            advance();
        }
    }
    if (!at_end() && (current() == 'e' || current() == 'E')) {
        advance();
        if (!at_end() && (current() == '+' || current() == '-')) {
            advance();
        }
        while (!at_end() && std::isdigit(static_cast<unsigned char>(current()))) {
            advance();
        }
    }

    Token tok;
    tok.kind = TokenKind::IntLiteral;
    tok.loc = loc;
    tok.text = source_.substr(start, pos_ - start);
    return tok;
}

Token Lexer::lex_string_literal() {
    auto loc = make_loc();
    uint32_t start = pos_;
    advance(); // skip opening "
    while (!at_end() && current() != '"') {
        if (current() == '\\') {
            advance();
        }
        advance();
    }
    if (!at_end()) {
        advance(); // skip closing "
    }
    Token tok;
    tok.kind = TokenKind::StringLiteral;
    tok.loc = loc;
    tok.text = source_.substr(start, pos_ - start);
    return tok;
}

Token Lexer::lex_system_identifier() {
    auto loc = make_loc();
    uint32_t start = pos_;
    advance(); // skip $
    while (!at_end() && (std::isalnum(static_cast<unsigned char>(current())) || current() == '_')) {
        advance();
    }
    Token tok;
    tok.kind = TokenKind::SystemIdentifier;
    tok.loc = loc;
    tok.text = source_.substr(start, pos_ - start);
    return tok;
}

Token Lexer::lex_escaped_identifier() {
    auto loc = make_loc();
    uint32_t start = pos_;
    advance(); // skip backslash
    while (!at_end() && !std::isspace(static_cast<unsigned char>(current()))) {
        advance();
    }
    Token tok;
    tok.kind = TokenKind::EscapedIdentifier;
    tok.loc = loc;
    tok.text = source_.substr(start, pos_ - start);
    return tok;
}

Token Lexer::lex_operator() {
    auto loc = make_loc();
    uint32_t start = pos_;
    char c = current();
    advance();

    auto one = [&](TokenKind k) -> Token {
        Token tok;
        tok.kind = k;
        tok.loc = loc;
        tok.text = source_.substr(start, pos_ - start);
        return tok;
    };

    auto try2 = [&](char c2, TokenKind k2, TokenKind k1) -> Token {
        if (!at_end() && current() == c2) {
            advance();
            Token tok;
            tok.kind = k2;
            tok.loc = loc;
            tok.text = source_.substr(start, pos_ - start);
            return tok;
        }
        return one(k1);
    };

    switch (c) {
    case '(': return one(TokenKind::LParen);
    case ')': return one(TokenKind::RParen);
    case '[': return one(TokenKind::LBracket);
    case ']': return one(TokenKind::RBracket);
    case '{': return one(TokenKind::LBrace);
    case '}': return one(TokenKind::RBrace);
    case ';': return one(TokenKind::Semicolon);
    case ',': return one(TokenKind::Comma);
    case '?': return one(TokenKind::Question);
    case '~':
        if (!at_end() && current() == '&') { advance(); return one(TokenKind::TildeAmp); }
        if (!at_end() && current() == '|') { advance(); return one(TokenKind::TildePipe); }
        if (!at_end() && current() == '^') { advance(); return one(TokenKind::TildeCaret); }
        return one(TokenKind::Tilde);
    case '@': return try2('@', TokenKind::AtAt, TokenKind::At);
    case '.':
        if (!at_end() && current() == '*') { advance(); return one(TokenKind::DotStar); }
        return one(TokenKind::Dot);
    case ':': return try2(':', TokenKind::ColonColon, TokenKind::Colon);
    case '+':
        if (!at_end() && current() == '+') { advance(); return one(TokenKind::PlusPlus); }
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::PlusEq); }
        return one(TokenKind::Plus);
    case '-':
        if (!at_end() && current() == '-') { advance(); return one(TokenKind::MinusMinus); }
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::MinusEq); }
        if (!at_end() && current() == '>') {
            advance();
            if (!at_end() && current() == '>') { advance(); return one(TokenKind::DashGtGt); }
            return one(TokenKind::Arrow);
        }
        return one(TokenKind::Minus);
    case '*':
        if (!at_end() && current() == '*') { advance(); return one(TokenKind::Power); }
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::StarEq); }
        if (!at_end() && current() == '>') { advance(); return one(TokenKind::StarGt); }
        return one(TokenKind::Star);
    case '/': return try2('=', TokenKind::SlashEq, TokenKind::Slash);
    case '%': return try2('=', TokenKind::PercentEq, TokenKind::Percent);
    case '^':
        if (!at_end() && current() == '~') { advance(); return one(TokenKind::CaretTilde); }
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::CaretEq); }
        return one(TokenKind::Caret);
    case '&':
        if (!at_end() && current() == '&') {
            advance();
            if (!at_end() && current() == '&') { advance(); return one(TokenKind::AmpAmpAmp); }
            return one(TokenKind::AmpAmp);
        }
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::AmpEq); }
        return one(TokenKind::Amp);
    case '|':
        if (!at_end() && current() == '|') { advance(); return one(TokenKind::PipePipe); }
        if (!at_end() && current() == '=') {
            advance();
            if (!at_end() && current() == '>') { advance(); return one(TokenKind::PipeEqGt); }
            return one(TokenKind::PipeEq);
        }
        if (!at_end() && current() == '-' && peek_char() == '>') {
            advance();
            advance();
            return one(TokenKind::PipeDashGt);
        }
        return one(TokenKind::Pipe);
    case '!':
        if (!at_end() && current() == '=') {
            advance();
            if (!at_end() && current() == '=') { advance(); return one(TokenKind::BangEqEq); }
            if (!at_end() && current() == '?') { advance(); return one(TokenKind::BangEqQuestion); }
            return one(TokenKind::BangEq);
        }
        return one(TokenKind::Bang);
    case '=':
        if (!at_end() && current() == '=') {
            advance();
            if (!at_end() && current() == '=') { advance(); return one(TokenKind::EqEqEq); }
            if (!at_end() && current() == '?') { advance(); return one(TokenKind::EqEqQuestion); }
            return one(TokenKind::EqEq);
        }
        if (!at_end() && current() == '>') { advance(); return one(TokenKind::EqGt); }
        return one(TokenKind::Eq);
    case '#':
        if (!at_end() && current() == '#') { advance(); return one(TokenKind::HashHash); }
        return one(TokenKind::Hash);
    default: break;
    }

    // Handle < and > with their shift variants
    if (c == '<') {
        return lex_angle_left(loc, start);
    }
    if (c == '>') {
        return lex_angle_right(loc, start);
    }

    diag_.error(loc, std::string("unexpected character '") + c + "'");
    Token tok;
    tok.kind = TokenKind::Error;
    tok.loc = loc;
    tok.text = source_.substr(start, pos_ - start);
    return tok;
}

Token Lexer::lex_angle_left(SourceLoc loc, uint32_t start) {
    auto one = [&](TokenKind k) -> Token {
        Token tok;
        tok.kind = k;
        tok.loc = loc;
        tok.text = source_.substr(start, pos_ - start);
        return tok;
    };
    if (at_end()) {
        return one(TokenKind::Lt);
    }
    if (current() == '=') {
        advance();
        return one(TokenKind::LtEq);
    }
    if (current() != '<') {
        return one(TokenKind::Lt);
    }
    advance(); // second <
    if (!at_end() && current() == '<') {
        advance();
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::LtLtLtEq); }
        return one(TokenKind::LtLtLt);
    }
    if (!at_end() && current() == '=') { advance(); return one(TokenKind::LtLtEq); }
    return one(TokenKind::LtLt);
}

Token Lexer::lex_angle_right(SourceLoc loc, uint32_t start) {
    auto one = [&](TokenKind k) -> Token {
        Token tok;
        tok.kind = k;
        tok.loc = loc;
        tok.text = source_.substr(start, pos_ - start);
        return tok;
    };
    if (at_end()) {
        return one(TokenKind::Gt);
    }
    if (current() == '=') {
        advance();
        return one(TokenKind::GtEq);
    }
    if (current() != '>') {
        return one(TokenKind::Gt);
    }
    advance(); // second >
    if (!at_end() && current() == '>') {
        advance();
        if (!at_end() && current() == '=') { advance(); return one(TokenKind::GtGtGtEq); }
        return one(TokenKind::GtGtGt);
    }
    if (!at_end() && current() == '=') { advance(); return one(TokenKind::GtGtEq); }
    return one(TokenKind::GtGt);
}

std::vector<Token> Lexer::lex_all() {
    std::vector<Token> tokens;
    while (true) {
        auto tok = next();
        tokens.push_back(tok);
        if (tok.is_eof()) {
            break;
        }
    }
    return tokens;
}

} // namespace delta
