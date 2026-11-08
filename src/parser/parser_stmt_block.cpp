#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"
#include "parser/parser.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

void Parser::MatchEndBlockLabel(std::string_view inline_label,
                                std::string_view prefix_label) {
  std::string_view block_name =
      inline_label.empty() ? prefix_label : inline_label;
  if (!Match(TokenKind::kColon)) return;
  auto end_id = ExpectIdentifier(Subclause("9.3.4"));
  if (block_name.empty()) {
    diag_.Error(end_id.loc,
                "end label '" + std::string(end_id.text) +
                    "' specified for unnamed block",
                Subclause("9.3.4"));
  } else if (end_id.text != block_name) {
    diag_.Error(end_id.loc,
                "end label '" + std::string(end_id.text) +
                    "' does not match block name '" + std::string(block_name) +
                    "'",
                Subclause("9.3.4"));
  }
}

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

static bool ClosesEnclosingConstruct(TokenKind tk) {
  static constexpr TokenKind kClosers[] = {
      TokenKind::kKwEnd,         TokenKind::kKwEndmodule,
      TokenKind::kKwEndpackage,  TokenKind::kKwEndinterface,
      TokenKind::kKwEndprogram,  TokenKind::kKwEndchecker,
      TokenKind::kKwEndclass,    TokenKind::kKwEndtask,
      TokenKind::kKwEndfunction, TokenKind::kKwEndcase,
      TokenKind::kKwEndgenerate, TokenKind::kKwJoin,
      TokenKind::kKwJoinAny,     TokenKind::kKwJoinNone};
  for (TokenKind closer : kClosers) {
    if (tk == closer) return true;
  }
  return false;
}

Stmt* Parser::ParseBlockStmt(std::string_view prefix_label) {
  TypeNameScope type_scope(*this);
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin, Subclause("9.3.1"));

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier(Subclause("9.3.4")).text;
  }
  bool before_stmts = true;
  while (!Check(TokenKind::kKwEnd) && !AtEnd() &&
         !ClosesEnclosingConstruct(CurrentToken().kind) &&
         !ClosesOpenRsCodeBlock(CurrentToken().kind)) {
    if (IsBlockVarDeclStart()) {
      if (!before_stmts) {
        diag_.Error(
            CurrentLoc(),
            "a declaration cannot follow a statement in a begin-end block",
            Subclause("9.3.1"));
      }
      ParseBlockVarDecls(stmt->stmts);
    } else if (!RejectMisplacedStmtLabel()) {
      before_stmts = false;
      auto* s = ParseStmt();
      if (s != nullptr) {
        stmt->stmts.push_back(s);
      }
    }
  }
  Expect(TokenKind::kKwEnd, Subclause("9.3.1"));

  MatchEndBlockLabel(stmt->label, prefix_label);
  stmt->range.end = CurrentLoc();
  return stmt;
}

Stmt* Parser::ParseForkStmt(std::string_view prefix_label) {
  TypeNameScope type_scope(*this);
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFork;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFork, Subclause("9.3.2"));

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier(Subclause("9.3.4")).text;
  }
  bool before_stmts = true;
  while (!Check(TokenKind::kKwJoin) && !Check(TokenKind::kKwJoinAny) &&
         !Check(TokenKind::kKwJoinNone) && !AtEnd() &&
         !ClosesEnclosingConstruct(CurrentToken().kind) &&
         !ClosesOpenRsCodeBlock(CurrentToken().kind)) {
    if (IsBlockVarDeclStart()) {
      if (!before_stmts) {
        diag_.Error(
            CurrentLoc(),
            "a declaration cannot follow a statement in a fork-join block",
            Subclause("9.3.2"));
      }
      ParseBlockVarDecls(stmt->fork_stmts);
    } else if (!RejectMisplacedStmtLabel()) {
      before_stmts = false;
      auto* s = ParseStmt();
      if (s != nullptr) stmt->fork_stmts.push_back(s);
    }
  }
  if (Check(TokenKind::kKwJoin) || Check(TokenKind::kKwJoinAny) ||
      Check(TokenKind::kKwJoinNone)) {
    stmt->join_kind = CurrentToken().kind;
    Consume();
  } else {
    diag_.Error(
        CurrentLoc(),
        "expected join, join_any or join_none to close the parallel block",
        Subclause("9.3.2"));
  }

  MatchEndBlockLabel(stmt->label, prefix_label);
  return stmt;
}

}  // namespace delta
