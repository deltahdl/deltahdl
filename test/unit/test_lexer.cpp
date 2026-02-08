#include <catch2/catch_test_macros.hpp>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> lex(const std::string& src) {
    static SourceManager mgr;
    auto fid = mgr.add_file("<test>", src);
    DiagEngine diag(mgr);
    Lexer lexer(mgr.file_content(fid), fid, diag);
    return lexer.lex_all();
}

TEST_CASE("Lex empty input", "[lexer]") {
    auto tokens = lex("");
    REQUIRE(tokens.size() == 1);
    REQUIRE(tokens[0].is_eof());
}

TEST_CASE("Lex keywords", "[lexer]") {
    auto tokens = lex("module endmodule");
    REQUIRE(tokens.size() == 3);
    REQUIRE(tokens[0].kind == TokenKind::KwModule);
    REQUIRE(tokens[1].kind == TokenKind::KwEndmodule);
    REQUIRE(tokens[2].is_eof());
}

TEST_CASE("Lex identifiers", "[lexer]") {
    auto tokens = lex("foo bar_123 _baz");
    REQUIRE(tokens.size() == 4);
    REQUIRE(tokens[0].kind == TokenKind::Identifier);
    REQUIRE(tokens[0].text == "foo");
    REQUIRE(tokens[1].text == "bar_123");
    REQUIRE(tokens[2].text == "_baz");
}

TEST_CASE("Lex integer literals", "[lexer]") {
    auto tokens = lex("42 8'hFF 4'b1010");
    REQUIRE(tokens.size() == 4);
    REQUIRE(tokens[0].kind == TokenKind::IntLiteral);
    REQUIRE(tokens[0].text == "42");
    REQUIRE(tokens[1].kind == TokenKind::IntLiteral);
    REQUIRE(tokens[1].text == "8'hFF");
    REQUIRE(tokens[2].kind == TokenKind::IntLiteral);
    REQUIRE(tokens[2].text == "4'b1010");
}

TEST_CASE("Lex string literals", "[lexer]") {
    auto tokens = lex("\"Hello, World!\"");
    REQUIRE(tokens.size() == 2);
    REQUIRE(tokens[0].kind == TokenKind::StringLiteral);
    REQUIRE(tokens[0].text == "\"Hello, World!\"");
}

TEST_CASE("Lex system identifiers", "[lexer]") {
    auto tokens = lex("$display $finish");
    REQUIRE(tokens.size() == 3);
    REQUIRE(tokens[0].kind == TokenKind::SystemIdentifier);
    REQUIRE(tokens[0].text == "$display");
    REQUIRE(tokens[1].text == "$finish");
}

TEST_CASE("Lex operators", "[lexer]") {
    auto tokens = lex("+ - * / == != <= >= << >> && ||");
    REQUIRE(tokens[0].kind == TokenKind::Plus);
    REQUIRE(tokens[1].kind == TokenKind::Minus);
    REQUIRE(tokens[2].kind == TokenKind::Star);
    REQUIRE(tokens[3].kind == TokenKind::Slash);
    REQUIRE(tokens[4].kind == TokenKind::EqEq);
    REQUIRE(tokens[5].kind == TokenKind::BangEq);
    REQUIRE(tokens[6].kind == TokenKind::LtEq);
    REQUIRE(tokens[7].kind == TokenKind::GtEq);
    REQUIRE(tokens[8].kind == TokenKind::LtLt);
    REQUIRE(tokens[9].kind == TokenKind::GtGt);
    REQUIRE(tokens[10].kind == TokenKind::AmpAmp);
    REQUIRE(tokens[11].kind == TokenKind::PipePipe);
}

TEST_CASE("Lex punctuation", "[lexer]") {
    auto tokens = lex("( ) [ ] { } ; , . :");
    REQUIRE(tokens[0].kind == TokenKind::LParen);
    REQUIRE(tokens[1].kind == TokenKind::RParen);
    REQUIRE(tokens[2].kind == TokenKind::LBracket);
    REQUIRE(tokens[3].kind == TokenKind::RBracket);
    REQUIRE(tokens[4].kind == TokenKind::LBrace);
    REQUIRE(tokens[5].kind == TokenKind::RBrace);
    REQUIRE(tokens[6].kind == TokenKind::Semicolon);
    REQUIRE(tokens[7].kind == TokenKind::Comma);
    REQUIRE(tokens[8].kind == TokenKind::Dot);
    REQUIRE(tokens[9].kind == TokenKind::Colon);
}

TEST_CASE("Lex skips comments", "[lexer]") {
    auto tokens = lex("a // comment\nb /* block */ c");
    REQUIRE(tokens.size() == 4);
    REQUIRE(tokens[0].text == "a");
    REQUIRE(tokens[1].text == "b");
    REQUIRE(tokens[2].text == "c");
}

TEST_CASE("Lex hello.sv", "[lexer]") {
    auto tokens = lex("module hello;\n  initial $display(\"Hello, DeltaHDL!\");\nendmodule\n");
    REQUIRE(tokens[0].kind == TokenKind::KwModule);
    REQUIRE(tokens[1].kind == TokenKind::Identifier);
    REQUIRE(tokens[1].text == "hello");
    REQUIRE(tokens[2].kind == TokenKind::Semicolon);
    REQUIRE(tokens[3].kind == TokenKind::KwInitial);
    REQUIRE(tokens[4].kind == TokenKind::SystemIdentifier);
    REQUIRE(tokens[4].text == "$display");
}

TEST_CASE("Lex source locations", "[lexer]") {
    auto tokens = lex("a\nb c");
    REQUIRE(tokens[0].loc.line == 1);
    REQUIRE(tokens[0].loc.column == 1);
    REQUIRE(tokens[1].loc.line == 2);
    REQUIRE(tokens[1].loc.column == 1);
    REQUIRE(tokens[2].loc.line == 2);
    REQUIRE(tokens[2].loc.column == 3);
}
