// The block statements of IEEE 1800-2023 §9.3 -- §9.3.1's sequential block,
// §9.3.2's parallel block, §9.3.4's block name after the closing keyword -- and
// §9.3.5's statement label, which may precede either block and is equivalent to
// naming it. These reach the rest of the statement parser through
// Parser::ParseStmt, Parser::IsBlockVarDeclStart and Parser::ParseBlockVarDecls
// only, all three declared in src/parser/parser.h, which is what made them the
// group to move out. The split keeps both files inside the 1000-line limit
// assert-no-oversized-source-files enforces.

#include "parser/parser.h"

namespace delta {

// CPD-dedup: a label preceding begin/fork is equivalent to a block name, so the
// matching name after end/join* may be the inline name or that prefix label.
// Validates the optional trailing ": name" against the effective block name.
struct ParserStmtBlockHelpers {
  static void MatchEndBlockLabel(Parser& p, std::string_view inline_label,
                                 std::string_view prefix_label) {
    std::string_view block_name =
        inline_label.empty() ? prefix_label : inline_label;
    if (p.Match(TokenKind::kColon)) {
      auto end_id = p.ExpectIdentifier(Subclause("9.3.4"));
      if (block_name.empty()) {
        p.diag_.Error(end_id.loc,
                      "end label '" + std::string(end_id.text) +
                          "' specified for unnamed block",
                      Subclause("9.3.4"));
      } else if (end_id.text != block_name) {
        p.diag_.Error(end_id.loc,
                      "end label '" + std::string(end_id.text) +
                          "' does not match block name '" +
                          std::string(block_name) + "'",
                      Subclause("9.3.4"));
      }
    }
  }
};

std::string_view Parser::TryParseStmtLabel() {
  if (!CheckIdentifier()) return {};
  auto saved = lexer_.SavePos();
  auto id_tok = Consume();
  if (Check(TokenKind::kColon)) {
    Consume();
    return id_tok.text;
  }
  lexer_.RestorePos(saved);
  return {};
}

// Reports the two placements §9.3.5 forbids a statement label, and answers
// whether it reported one: "A label can be specified before any procedural
// statement (any non-declaration statement that can appear inside a begin-end
// block)", and "A label cannot appear before the end, join, join_any, or
// join_none, as these keywords do not form a statement". Call it at the head of
// a body loop rather than from Parser::ParseStmt, where the label is taken,
// because each recovery is the loop's: the closing keyword has to survive for
// the loop's own terminator test, and the declaration has to reach the loop's
// Parser::ParseBlockVarDecls branch. Consumes the label and its colon when it
// reports, so the next iteration reads what the label stood before and the loop
// makes progress; restores the position otherwise, leaving a legal label for
// Parser::TryParseStmtLabel. A label in a single-statement position, such as an
// if branch, is not examined, since nothing there re-reads what it would leave.
bool Parser::RejectMisplacedStmtLabel() {
  if (!CheckIdentifier()) return false;
  auto saved = lexer_.SavePos();
  auto id_tok = Consume();
  if (!Match(TokenKind::kColon)) {
    lexer_.RestorePos(saved);
    return false;
  }
  if (Check(TokenKind::kKwEnd) || Check(TokenKind::kKwJoin) ||
      Check(TokenKind::kKwJoinAny) || Check(TokenKind::kKwJoinNone)) {
    diag_.Error(id_tok.loc,
                "a statement label cannot appear before '" +
                    std::string(CurrentToken().text) +
                    "', which does not form a statement",
                Subclause("9.3.5"));
    return true;
  }
  if (IsBlockVarDeclStart()) {
    diag_.Error(id_tok.loc,
                "a statement label cannot appear before a declaration; a label "
                "may precede only a procedural statement",
                Subclause("9.3.5"));
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

Stmt* Parser::ParseBlockStmt(std::string_view prefix_label) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin, Subclause("9.3.1"));

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier(Subclause("9.3.4")).text;
  }
  while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmt->stmts);
    } else if (!RejectMisplacedStmtLabel()) {
      auto* s = ParseStmt();
      if (s != nullptr) {
        stmt->stmts.push_back(s);
      }
    }
  }
  Expect(TokenKind::kKwEnd, Subclause("9.3.1"));

  ParserStmtBlockHelpers::MatchEndBlockLabel(*this, stmt->label, prefix_label);
  stmt->range.end = CurrentLoc();
  return stmt;
}

// Answers whether tk closes a construct a par_block can stand inside. The
// first seven are the keywords Parser::Synchronize enumerates in
// src/parser/parser.cpp; endtask and endfunction join them because §9.3.2
// makes a par_block a statement_or_null, so a fork can stand in a task or a
// function body. endcase and endgenerate join them because a case item's body
// is a statement_or_null and a generate region holds an initial block. The
// eight other `end` keywords were read against Annex A and left out.
static bool ClosesEnclosingConstruct(TokenKind tk) {
  static constexpr TokenKind kClosers[] = {
      TokenKind::kKwEnd,         TokenKind::kKwEndmodule,
      TokenKind::kKwEndpackage,  TokenKind::kKwEndinterface,
      TokenKind::kKwEndprogram,  TokenKind::kKwEndchecker,
      TokenKind::kKwEndclass,    TokenKind::kKwEndtask,
      TokenKind::kKwEndfunction, TokenKind::kKwEndcase,
      TokenKind::kKwEndgenerate};
  for (TokenKind closer : kClosers) {
    if (tk == closer) return true;
  }
  return false;
}

Stmt* Parser::ParseForkStmt(std::string_view prefix_label) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFork;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFork, Subclause("9.3.2"));

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier(Subclause("9.3.4")).text;
  }
  // Stop at a token that closes an enclosing construct as well as at the three
  // join keywords. Without that stop, Parser::ParsePrimaryExpr consumes the
  // token as a failed expression under §11.2, so the §9.3.2 report below could
  // only ever fire at end of input and the §11.2 cascade over the enclosing
  // block would stay.
  while (!Check(TokenKind::kKwJoin) && !Check(TokenKind::kKwJoinAny) &&
         !Check(TokenKind::kKwJoinNone) && !AtEnd() &&
         !ClosesEnclosingConstruct(CurrentToken().kind)) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmt->fork_stmts);
    } else if (!RejectMisplacedStmtLabel()) {
      auto* s = ParseStmt();
      if (s != nullptr) stmt->fork_stmts.push_back(s);
    }
  }
  if (Check(TokenKind::kKwJoin) || Check(TokenKind::kKwJoinAny) ||
      Check(TokenKind::kKwJoinNone)) {
    stmt->join_kind = CurrentToken().kind;
    Consume();
  } else {
    // Leave the token for the enclosing production, which is what lets an
    // enclosing begin find its end and a module find its endmodule. Leave
    // stmt->join_kind at the TokenKind::kKwJoin default the declaration of
    // Stmt::join_kind in src/parser/ast_stmt.h gives rather than recording a
    // token §9.3.2 does not admit as a join_keyword.
    diag_.Error(
        CurrentLoc(),
        "expected join, join_any or join_none to close the parallel block",
        Subclause("9.3.2"));
  }

  ParserStmtBlockHelpers::MatchEndBlockLabel(*this, stmt->label, prefix_label);
  return stmt;
}

}  // namespace delta
