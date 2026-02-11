#include "parser/parser.h"

namespace delta {

// --- §17 Checker declaration ---

ModuleDecl* Parser::ParseCheckerDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kChecker;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwChecker);
  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  // Checker body — reuse module item parsing.
  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    ParseModuleItem(decl->items);
  }
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndchecker);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

// --- §18 Randcase statement ---

Stmt* Parser::ParseRandcaseStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRandcase);

  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    auto* weight = ParseExpr();
    Expect(TokenKind::kColon);
    auto* body = ParseStmt();
    stmt->randcase_items.push_back({weight, body});
  }
  Expect(TokenKind::kKwEndcase);
  stmt->range.end = CurrentLoc();
  return stmt;
}

// --- §18.17 Randsequence statement ---

Stmt* Parser::ParseRandsequenceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;  // reuse for stub
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRandsequence);
  // Optional production name: randsequence(name)
  if (Check(TokenKind::kLParen)) {
    Consume();
    if (!Check(TokenKind::kRParen)) Consume();  // production name
    Expect(TokenKind::kRParen);
  }
  // Skip all tokens until endsequence.
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndsequence);
  stmt->range.end = CurrentLoc();
  return stmt;
}

// --- §19 Covergroup declaration ---

// Skip tokens until we see a matching '}' for a '{' that was consumed.
static void SkipBraceBlock(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLBrace)) ++depth;
    if (lexer.Peek().Is(TokenKind::kRBrace)) --depth;
    if (depth > 0) lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kRBrace)) lexer.Next();
}

// Skip a coverpoint or cross definition including optional bin block.
static void SkipCoverpointBody(Lexer& lexer) {
  // Skip until ';' or '{'.
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kLBrace) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kLBrace)) {
    lexer.Next();  // consume '{'
    SkipBraceBlock(lexer);
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

void Parser::ParseCovergroupDecl(std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCovergroupDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCovergroup);
  item->name = Expect(TokenKind::kIdentifier).text;

  // Optional sampling event: @(event) or @@(event).
  if (Match(TokenKind::kAt) || Match(TokenKind::kAtAt)) {
    Expect(TokenKind::kLParen);
    ParseEventList();
    Expect(TokenKind::kRParen);
  }
  Expect(TokenKind::kSemicolon);

  // Covergroup body — skip for now (just consume to endgroup).
  while (!Check(TokenKind::kKwEndgroup) && !AtEnd()) {
    SkipCovergroupItem();
  }
  Expect(TokenKind::kKwEndgroup);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  items.push_back(item);
}

static bool IsOptionKeyword(std::string_view text) {
  return text == "option" || text == "type_option";
}

static bool IsCoverpointOrCross(TokenKind tk) {
  return tk == TokenKind::kKwCoverpoint || tk == TokenKind::kKwCross;
}

static void SkipToSemiOrEnd(Lexer& lexer, TokenKind end_kw) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) && !lexer.Peek().Is(end_kw) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

void Parser::SkipCovergroupItem() {
  // option.xxx = expr; or type_option.xxx = expr;
  if (Check(TokenKind::kIdentifier) && IsOptionKeyword(CurrentToken().text)) {
    SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
    return;
  }
  // coverpoint or cross keyword directly.
  if (IsCoverpointOrCross(CurrentToken().kind)) {
    Consume();
    SkipCoverpointBody(lexer_);
    return;
  }
  // Identifier — could be label:coverpoint, or just an expression coverpoint.
  if (Check(TokenKind::kIdentifier)) {
    Consume();
    if (Match(TokenKind::kColon) && IsCoverpointOrCross(CurrentToken().kind)) {
      Consume();
    }
    SkipCoverpointBody(lexer_);
    return;
  }
  // Anything else — skip to semicolon.
  SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
}

}  // namespace delta
