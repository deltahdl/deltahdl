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

// Answers whether tk closes a construct a block can stand inside. §9.3.1 makes
// a seq_block a statement_or_null and §9.3.2 makes a par_block one, so both
// kinds reach the same enclosing constructs and both loops below stop at the
// same tokens.
//
// The first seven are the keywords Parser::Synchronize enumerates in
// src/parser/parser.cpp. endtask and endfunction join them because a block can
// stand in a task or a function body. endcase joins them because a case item's
// body is a statement_or_null. endgenerate joins them because a generate region
// holds an initial block: A.4.2 gives `generate_region ::= generate
// { generate_item } endgenerate` and no generate_item is a statement, so a
// block reaches one through the initial, always or final construct that holds
// it rather than directly.
//
// The three join keywords are here because §9.3.2 gives `par_block ::= fork
// [ : block_identifier ] { block_item_declaration } { statement_or_null }
// join_keyword`, so a seq_block left open inside a fork is closed by one of
// them and by no `end` at all. Parser::ParseForkStmt tests them first as its
// own terminators, so the three entries decide nothing there.
//
// `end` is here for the same reason in reverse: it closes the seq_block a
// par_block can stand inside. Parser::ParseBlockStmt tests it first as its own
// terminator, so that entry decides nothing there.
//
// Seven of the nineteen `end` keywords Table B.1 lists are left out, each
// settled against Annex A: endspecify (A.7.1's specify_item reaches no
// statement), endclocking (A.6.11's clocking_item reaches none), endproperty
// (A.2.10's property_expr reaches none), endgroup (A.2.11's
// coverage_spec_or_option reaches none), endconfig (A.1.5's
// config_rule_statement is configuration vocabulary), and endprimitive with
// endtable (A.5.3's udp_initial_statement takes `output_port_identifier =
// init_val ;` rather than a statement). endsequence is the one left out that a
// statement does reach, through A.6.12's `rs_code_block ::= { {
// data_declaration } { statement_or_null } }`; #3162 records why it is not
// here.
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
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin, Subclause("9.3.1"));

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier(Subclause("9.3.4")).text;
  }
  // Stop at a token that closes an enclosing construct as well as at `end`, for
  // the reason Parser::ParseForkStmt below stops at one: without it
  // Parser::ParsePrimaryExpr consumes the token as a failed expression under
  // §11.2, so `begin` left open before an `endcase` drew that report on the
  // `endcase`, another on the `endmodule` behind it, the §9.3.1 report below at
  // end of input rather than at the token at fault, and the enclosing case
  // statement's own §12.5 report for the `endcase` it never saw. Four reports
  // for one missing `end`.
  while (!Check(TokenKind::kKwEnd) && !AtEnd() &&
         !ClosesEnclosingConstruct(CurrentToken().kind)) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmt->stmts);
    } else if (!RejectMisplacedStmtLabel()) {
      auto* s = ParseStmt();
      if (s != nullptr) {
        stmt->stmts.push_back(s);
      }
    }
  }
  // Leave the token for the enclosing production when it is one of the closers,
  // which is what lets the case statement find its endcase and the module its
  // endmodule. Expect reports without consuming, so the closer survives.
  Expect(TokenKind::kKwEnd, Subclause("9.3.1"));

  ParserStmtBlockHelpers::MatchEndBlockLabel(*this, stmt->label, prefix_label);
  stmt->range.end = CurrentLoc();
  return stmt;
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
