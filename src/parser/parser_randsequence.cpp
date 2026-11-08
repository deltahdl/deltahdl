#include <cstddef>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

namespace {

void ReportNonDataCodeBlockDecl(const Stmt* decl, SourceLoc loc,
                                DiagEngine& diag) {
  const bool kIsLet = decl->kind == StmtKind::kBlockItemDecl &&
                      decl->decl_item->kind == ModuleItemKind::kLetDecl;
  if (!decl->var_is_param && !kIsLet) return;
  diag.Error(loc,
             "a randsequence code block declares data, never a parameter or "
             "a let",
             Subclause("A.6.12"));
}

}  // namespace

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
  if (stmt->randcase_items.empty()) {
    diag_.Error(CurrentLoc(), "a randcase statement holds at least one item",
                Subclause("A.6.7"));
  }
  Expect(TokenKind::kKwEndcase, Subclause("18.16"));
  stmt->range.end = CurrentLoc();
  return stmt;
}

RsProductionItem Parser::ParseRsProductionItem() {
  RsProductionItem item;
  Token name = ExpectIdentifier(Subclause("18.17"));
  item.name = name.text;
  item.loc = name.loc;
  if (Check(TokenKind::kLParen)) {
    Consume();
    if (!Check(TokenKind::kRParen) && !Check(TokenKind::kKwDefault)) {
      auto* call = arena_.Create<Expr>();
      if (Check(TokenKind::kDot)) {
        ParseTrailingNamedArgs(call);
      } else {
        ParseCallArgs(call);
      }
      item.args = std::move(call->args);
      item.arg_names = std::move(call->arg_names);
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
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(rs_code_block_depth_);

  bool before_stmts = true;
  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    if (!IsBlockVarDeclStart()) {
      before_stmts = false;
      stmts.push_back(ParseStmt());
      continue;
    }
    const SourceLoc kLoc = CurrentLoc();
    if (!before_stmts) {
      diag_.Error(kLoc,
                  "a declaration cannot follow a statement in a randsequence "
                  "code block",
                  Subclause("A.6.12"));
    }
    const size_t kFirst = stmts.size();
    ParseBlockVarDecls(stmts);
    ReportNonDataCodeBlockDecl(stmts[kFirst], kLoc, diag_);
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
  if (prod.case_items.empty()) {
    diag_.Error(CurrentLoc(), "a case production holds at least one item",
                Subclause("A.6.12"));
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
    if (rule.weight->kind != ExprKind::kIntegerLiteral &&
        !IsPsIdentifier(rule.weight)) {
      diag_.Error(rule.weight->range.start,
                  "a rule's weight written without parentheses is an integral "
                  "number or an identifier, which a package scope may qualify; "
                  "any other expression is parenthesized",
                  Subclause("A.6.12"));
    }
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

  bool has_return_type = AtDataTypeOrVoid();
  if (has_return_type && Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    Consume();
    has_return_type = !Check(TokenKind::kLParen) && !Check(TokenKind::kColon);
    lexer_.RestorePos(saved);
  }
  if (has_return_type &&
      (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned) ||
       Check(TokenKind::kLBracket))) {
    diag_.Error(CurrentLoc(),
                "a randsequence production return type shall be a data type or "
                "'void', and a signing or a packed dimension does not stand as "
                "one on its own",
                Subclause("18.17"));
  }
  if (has_return_type) {
    prod.return_type = ParseFunctionReturnType();
    prod.has_return_type = true;
  }

  prod.name = ExpectIdentifier(Subclause("18.17")).text;

  if (Check(TokenKind::kLParen)) {
    prod.has_ports = true;
    const SourceLoc kOpen = CurrentLoc();
    prod.ports = ParseFunctionArgs(true);
    if (prod.ports.empty()) {
      diag_.Error(kOpen,
                  "a production's parentheses enclose at least one formal "
                  "argument; a production with none is written without them",
                  Subclause("A.6.12"));
    }
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
    if (lexer_.SavePos().pos == before) break;
  }
  if (stmt->rs_productions.empty()) {
    diag_.Error(CurrentLoc(),
                "a randsequence statement holds at least one production",
                Subclause("A.6.12"));
  }

  Expect(TokenKind::kKwEndsequence, Subclause("18.17"));
  stmt->range.end = CurrentLoc();
  return stmt;
}

}  // namespace delta
