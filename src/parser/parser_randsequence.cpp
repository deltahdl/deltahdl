// §18.16's randcase statement and §18.17's randsequence, parsed: the
// production and rule lists of Syntax 18-13, the if-else of §18.17.2, the case
// of §18.17.3, the repeat of §18.17.4 and the rand join of §18.17.5, together
// with the `:=` and `:/` scanning the weights of §18.17.1 need.
//
// Every function here is a Parser:: member declared in parser/parser.h and
// reached from a dispatcher there, so the move out of parser_verify.cpp
// changed no declaration and no call site. The two clauses travel together
// because the simulator keeps them together for the same reason:
// src/simulator/stmt_exec_randsequence.cpp answers §18.16 and §18.17 in one
// file, randcase being the weighted selection randsequence's rule lists are
// built on.

#include <vector>

#include "parser/parser.h"

namespace delta {

Stmt* Parser::ParseRandcaseStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRandcase, Subclause("18.16"));

  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    auto* weight = ParseExpr();
    Expect(TokenKind::kColon, Subclause("18.16"));
    auto* body = ParseStmt();
    stmt->randcase_items.push_back({weight, body});
  }
  Expect(TokenKind::kKwEndcase, Subclause("18.16"));
  stmt->range.end = CurrentLoc();
  return stmt;
}

RsProductionItem Parser::ParseRsProductionItem() {
  RsProductionItem item;
  item.name = ExpectIdentifier(Subclause("18.17")).text;
  if (Check(TokenKind::kLParen)) {
    Consume();
    if (!Check(TokenKind::kRParen)) {
      item.args.push_back(ParseExpr());
      while (Match(TokenKind::kComma)) {
        item.args.push_back(ParseExpr());
      }
    }
    Expect(TokenKind::kRParen, Subclause("18.17.7"));
  }
  return item;
}

RsCaseItem Parser::ParseRsCaseItem() {
  RsCaseItem ci;
  if (Match(TokenKind::kKwDefault)) {
    ci.is_default = true;
    Match(TokenKind::kColon);
    ci.item = ParseRsProductionItem();
    Expect(TokenKind::kSemicolon, Subclause("18.17.3"));
  } else {
    ci.patterns.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      ci.patterns.push_back(ParseExpr());
    }
    Expect(TokenKind::kColon, Subclause("18.17.3"));
    ci.item = ParseRsProductionItem();
    Expect(TokenKind::kSemicolon, Subclause("18.17.3"));
  }
  return ci;
}

void Parser::ParseRsCodeBlockStmts(std::vector<Stmt*>& stmts) {
  // Records that a right brace now closes something, so that a block left open
  // inside this code block stops at it rather than taking it for a statement.
  // Parser::ClosesOpenRsCodeBlock in src/parser/parser.h is what reads the
  // count, and the guard restores it however this returns.
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(rs_code_block_depth_);

  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmts);
    } else {
      stmts.push_back(ParseStmt());
    }
  }
}

void Parser::ParseRsProdIf(RsProd& prod) {
  prod.kind = RsProdKind::kIf;
  Consume();
  Expect(TokenKind::kLParen, Subclause("18.17.2"));
  prod.condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("18.17.2"));
  prod.if_true = ParseRsProductionItem();
  if (Match(TokenKind::kKwElse)) {
    prod.has_else = true;
    prod.if_false = ParseRsProductionItem();
  }
}

void Parser::ParseRsProdRepeat(RsProd& prod) {
  prod.kind = RsProdKind::kRepeat;
  Consume();
  Expect(TokenKind::kLParen, Subclause("18.17.4"));
  prod.repeat_count = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("18.17.4"));
  prod.repeat_item = ParseRsProductionItem();
}

void Parser::ParseRsProdCase(RsProd& prod) {
  prod.kind = RsProdKind::kCase;
  Consume();
  Expect(TokenKind::kLParen, Subclause("18.17.3"));
  prod.case_expr = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("18.17.3"));
  bool seen_default = false;
  // 18.17.3: a case production statement shall contain at most one default
  // item; flag any additional default as illegal.
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    auto item_loc = CurrentLoc();
    bool is_default_here = Check(TokenKind::kKwDefault);
    prod.case_items.push_back(ParseRsCaseItem());
    if (is_default_here && seen_default) {
      diag_.Error(item_loc,
                  "case production shall have at most one 'default' item",
                  Subclause("18.17.3"));
    }
    if (is_default_here) seen_default = true;
  }
  Expect(TokenKind::kKwEndcase, Subclause("18.17.3"));
}

RsProd Parser::ParseRsProd() {
  RsProd prod;

  if (Check(TokenKind::kLBrace)) {
    prod.kind = RsProdKind::kCodeBlock;
    Consume();
    ParseRsCodeBlockStmts(prod.code_stmts);
    Expect(TokenKind::kRBrace, Subclause("18.17"));
  } else if (Check(TokenKind::kKwIf)) {
    ParseRsProdIf(prod);
  } else if (Check(TokenKind::kKwRepeat)) {
    ParseRsProdRepeat(prod);
  } else if (Check(TokenKind::kKwCase)) {
    ParseRsProdCase(prod);
  } else {
    prod.kind = RsProdKind::kItem;
    prod.item = ParseRsProductionItem();
  }
  return prod;
}

bool Parser::CheckColonEq() {
  if (!Check(TokenKind::kColon)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool result = Check(TokenKind::kEq);
  lexer_.RestorePos(saved);
  return result;
}

bool Parser::MatchColonEq() {
  if (!Check(TokenKind::kColon)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  if (Check(TokenKind::kEq)) {
    Consume();
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

// 18.5.3: the distribution weight operator ":/" lexes as a colon immediately
// followed by a slash. CheckColonSlash peeks for that pair without consuming;
// MatchColonSlash consumes it on a match.
bool Parser::CheckColonSlash() {
  if (!Check(TokenKind::kColon)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool result = Check(TokenKind::kSlash);
  lexer_.RestorePos(saved);
  return result;
}

bool Parser::MatchColonSlash() {
  if (!Check(TokenKind::kColon)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  if (Check(TokenKind::kSlash)) {
    Consume();
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

void Parser::ParseRsRuleRandJoin(RsRule& rule) {
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kKwJoin)) {
    lexer_.RestorePos(saved);
    return;
  }
  Consume();
  rule.is_rand_join = true;
  if (Check(TokenKind::kLParen)) {
    Consume();
    rule.rand_join_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("18.17.5"));
  }
  rule.rand_join_items.push_back(ParseRsProductionItem());
  rule.rand_join_items.push_back(ParseRsProductionItem());
  while (CheckIdentifier() && !CheckColonEq() &&
         !Check(TokenKind::kSemicolon) && !Check(TokenKind::kPipe)) {
    rule.rand_join_items.push_back(ParseRsProductionItem());
  }
}

void Parser::ParseRsRuleWeight(RsRule& rule) {
  if (Check(TokenKind::kLParen)) {
    Consume();
    rule.weight = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("18.17.1"));
  } else {
    rule.weight = ParsePrimaryExpr();
  }
  if (Check(TokenKind::kLBrace)) {
    Consume();
    ParseRsCodeBlockStmts(rule.weight_code);
    Expect(TokenKind::kRBrace, Subclause("18.17.1"));
  }
}

RsRule Parser::ParseRsRule() {
  RsRule rule;

  if (Check(TokenKind::kKwRand)) {
    ParseRsRuleRandJoin(rule);
  }

  if (!rule.is_rand_join) {
    rule.prods.push_back(ParseRsProd());
    while (!CheckColonEq() && !Check(TokenKind::kSemicolon) &&
           !Check(TokenKind::kPipe) && !AtEnd()) {
      if (!CheckIdentifier() && !Check(TokenKind::kLBrace) &&
          !Check(TokenKind::kKwIf) && !Check(TokenKind::kKwRepeat) &&
          !Check(TokenKind::kKwCase)) {
        break;
      }
      rule.prods.push_back(ParseRsProd());
    }
  }

  if (MatchColonEq()) {
    ParseRsRuleWeight(rule);
  }

  return rule;
}

RsProduction Parser::ParseRsProduction() {
  RsProduction prod;

  // Syntax 18-13 (§18.17): `rs_production ::= [ data_type_or_void ]
  // rs_production_identifier [ ( tf_port_list ) ] : rs_rule { | rs_rule } ;`.
  // A return type is present when the production opens on a data_type_or_void,
  // which AtDataTypeOrVoid answers for the whole of A.2.2.1 rather than for
  // its keyword cases alone. §18.17.7 sizes a returned value by that type.
  //
  // An identifier naming a declared type is either that return type or the
  // production's own name, and the token after it decides which: Syntax 18-13
  // admits only `(` or `:` after the rs_production_identifier. So `word v :`
  // returns `word` from a production `v`, `word :` names a production `word`,
  // and a scoped type name, followed by `::`, stays a return type.
  bool has_return_type = AtDataTypeOrVoid();
  if (has_return_type && Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    Consume();
    has_return_type = !Check(TokenKind::kLParen) && !Check(TokenKind::kColon);
    lexer_.RestorePos(saved);
  }
  if (has_return_type) {
    prod.return_type = ParseFunctionReturnType();
    prod.has_return_type = true;
  }

  prod.name = ExpectIdentifier(Subclause("18.17")).text;

  // §18.17.7: productions that accept data declare a tf_port_list of formal
  // arguments, using the same syntax as a task prototype. Parse and retain the
  // formals so the value-passing engine can bind actual arguments to them.
  if (Check(TokenKind::kLParen)) {
    prod.has_ports = true;
    prod.ports = ParseFunctionArgs(true);
  }

  Expect(TokenKind::kColon, Subclause("18.17"));

  prod.rules.push_back(ParseRsRule());
  while (Match(TokenKind::kPipe)) {
    prod.rules.push_back(ParseRsRule());
  }

  Expect(TokenKind::kSemicolon, Subclause("18.17"));
  return prod;
}

Stmt* Parser::ParseRandsequenceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRandsequence;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRandsequence, Subclause("18.17"));

  Expect(TokenKind::kLParen, Subclause("18.17"));
  if (CheckIdentifier()) {
    stmt->rs_top_production = Consume().text;
  }
  Expect(TokenKind::kRParen, Subclause("18.17"));

  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    stmt->rs_productions.push_back(ParseRsProduction());
    // Missing endsequence: a token that cannot start a production (e.g. the
    // enclosing end/endmodule) reaches here and ParseRsProduction consumes
    // nothing. Stop and let the Expect below report the missing endsequence.
    if (lexer_.SavePos().pos == before) break;
  }

  Expect(TokenKind::kKwEndsequence, Subclause("18.17"));
  stmt->range.end = CurrentLoc();
  return stmt;
}

}  // namespace delta
