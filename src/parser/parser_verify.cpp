#include "parser/parser.h"

namespace delta {

static void SkipParenContents(Lexer& lexer);

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

// §A.6.12: rs_production_item ::= identifier [ ( list_of_arguments ) ]
RsProductionItem Parser::ParseRsProductionItem() {
  RsProductionItem item;
  item.name = ExpectIdentifier().text;
  if (Check(TokenKind::kLParen)) {
    Consume();
    if (!Check(TokenKind::kRParen)) {
      item.args.push_back(ParseExpr());
      while (Match(TokenKind::kComma)) {
        item.args.push_back(ParseExpr());
      }
    }
    Expect(TokenKind::kRParen);
  }
  return item;
}

// §A.6.12: rs_case_item ::= expr {, expr} : item ; | default [:] item ;
RsCaseItem Parser::ParseRsCaseItem() {
  RsCaseItem ci;
  if (Match(TokenKind::kKwDefault)) {
    ci.is_default = true;
    Match(TokenKind::kColon);  // Optional ':'
    ci.item = ParseRsProductionItem();
    Expect(TokenKind::kSemicolon);
  } else {
    ci.patterns.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      ci.patterns.push_back(ParseExpr());
    }
    Expect(TokenKind::kColon);
    ci.item = ParseRsProductionItem();
    Expect(TokenKind::kSemicolon);
  }
  return ci;
}

// §A.6.12: rs_prod ::= item | code_block | if_else | repeat | case
RsProd Parser::ParseRsProd() {
  RsProd prod;

  // rs_code_block: { {data_declaration} {statement_or_null} }
  if (Check(TokenKind::kLBrace)) {
    prod.kind = RsProdKind::kCodeBlock;
    Consume();  // '{'
    while (!Check(TokenKind::kRBrace) && !AtEnd()) {
      if (IsBlockVarDeclStart()) {
        ParseBlockVarDecls(prod.code_stmts);
      } else {
        prod.code_stmts.push_back(ParseStmt());
      }
    }
    Expect(TokenKind::kRBrace);
    return prod;
  }

  // rs_if_else: if ( expr ) item [ else item ]
  if (Check(TokenKind::kKwIf)) {
    prod.kind = RsProdKind::kIf;
    Consume();
    Expect(TokenKind::kLParen);
    prod.condition = ParseExpr();
    Expect(TokenKind::kRParen);
    prod.if_true = ParseRsProductionItem();
    if (Match(TokenKind::kKwElse)) {
      prod.has_else = true;
      prod.if_false = ParseRsProductionItem();
    }
    return prod;
  }

  // rs_repeat: repeat ( expr ) item
  if (Check(TokenKind::kKwRepeat)) {
    prod.kind = RsProdKind::kRepeat;
    Consume();
    Expect(TokenKind::kLParen);
    prod.repeat_count = ParseExpr();
    Expect(TokenKind::kRParen);
    prod.repeat_item = ParseRsProductionItem();
    return prod;
  }

  // rs_case: case ( expr ) case_item+ endcase
  if (Check(TokenKind::kKwCase)) {
    prod.kind = RsProdKind::kCase;
    Consume();
    Expect(TokenKind::kLParen);
    prod.case_expr = ParseExpr();
    Expect(TokenKind::kRParen);
    while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
      prod.case_items.push_back(ParseRsCaseItem());
    }
    Expect(TokenKind::kKwEndcase);
    return prod;
  }

  // rs_production_item: identifier [ ( args ) ]
  prod.kind = RsProdKind::kItem;
  prod.item = ParseRsProductionItem();
  return prod;
}

// §A.6.12: rs_rule ::= production_list [ := weight [code_block] ]
RsRule Parser::ParseRsRule() {
  RsRule rule;

  // Helper: check if current position is ':=' (colon + eq).
  auto IsAtColonEq = [&]() {
    if (!Check(TokenKind::kColon)) return false;
    auto saved = lexer_.SavePos();
    Consume();
    bool result = Check(TokenKind::kEq);
    lexer_.RestorePos(saved);
    return result;
  };

  // Helper: match ':=' (colon + eq), consuming both if matched.
  auto MatchColonEq = [&]() {
    if (!Check(TokenKind::kColon)) return false;
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kEq)) {
      Consume();
      return true;
    }
    lexer_.RestorePos(saved);
    return false;
  };

  // Check for rand join prefix.
  if (Check(TokenKind::kKwRand)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kKwJoin)) {
      Consume();
      rule.is_rand_join = true;
      // Optional ( expression )
      if (Check(TokenKind::kLParen)) {
        Consume();
        rule.rand_join_expr = ParseExpr();
        Expect(TokenKind::kRParen);
      }
      // Two or more production items.
      rule.rand_join_items.push_back(ParseRsProductionItem());
      rule.rand_join_items.push_back(ParseRsProductionItem());
      while (CheckIdentifier() && !IsAtColonEq() &&
             !Check(TokenKind::kSemicolon) && !Check(TokenKind::kPipe)) {
        rule.rand_join_items.push_back(ParseRsProductionItem());
      }
    } else {
      lexer_.RestorePos(saved);
      // Not rand join — parse as normal prod sequence.
    }
  }

  if (!rule.is_rand_join) {
    // Parse sequence of rs_prod.
    rule.prods.push_back(ParseRsProd());
    // Continue as long as the next token can start an rs_prod:
    // identifier, '{', 'if', 'repeat', 'case'
    while (!IsAtColonEq() && !Check(TokenKind::kSemicolon) &&
           !Check(TokenKind::kPipe) && !AtEnd()) {
      // Must be start of an rs_prod.
      if (CheckIdentifier() || Check(TokenKind::kLBrace) ||
          Check(TokenKind::kKwIf) || Check(TokenKind::kKwRepeat) ||
          Check(TokenKind::kKwCase)) {
        rule.prods.push_back(ParseRsProd());
      } else {
        break;
      }
    }
  }

  // Optional := weight_specification [code_block]
  if (MatchColonEq()) {
    // rs_weight_specification: number | identifier | ( expr )
    if (Check(TokenKind::kLParen)) {
      Consume();
      rule.weight = ParseExpr();
      Expect(TokenKind::kRParen);
    } else {
      rule.weight = ParsePrimaryExpr();
    }
    // Optional code block after weight.
    if (Check(TokenKind::kLBrace)) {
      Consume();
      while (!Check(TokenKind::kRBrace) && !AtEnd()) {
        if (IsBlockVarDeclStart()) {
          ParseBlockVarDecls(rule.weight_code);
        } else {
          rule.weight_code.push_back(ParseStmt());
        }
      }
      Expect(TokenKind::kRBrace);
    }
  }

  return rule;
}

// §A.6.12: rs_production ::= [type] name [(ports)] : rule { | rule } ;
RsProduction Parser::ParseRsProduction() {
  RsProduction prod;

  // Optional data_type_or_void prefix (before identifier).
  // We check for void or a known type keyword before the production name.
  if (Check(TokenKind::kKwVoid)) {
    Consume();
    prod.has_return_type = true;
  } else if (Check(TokenKind::kKwInt) || Check(TokenKind::kKwBit) ||
             Check(TokenKind::kKwLogic) || Check(TokenKind::kKwByte) ||
             Check(TokenKind::kKwShortint) || Check(TokenKind::kKwLongint) ||
             Check(TokenKind::kKwInteger) || Check(TokenKind::kKwString) ||
             Check(TokenKind::kKwReal) || Check(TokenKind::kKwShortreal) ||
             Check(TokenKind::kKwRealtime) || Check(TokenKind::kKwTime)) {
    Consume();
    prod.has_return_type = true;
  }

  prod.name = ExpectIdentifier().text;

  // Optional ( tf_port_list )
  if (Check(TokenKind::kLParen)) {
    prod.has_ports = true;
    Consume();
    // Skip port list contents — not needed for A.6.12 scope.
    SkipParenContents(lexer_);
  }

  Expect(TokenKind::kColon);

  // Parse rules separated by '|'.
  prod.rules.push_back(ParseRsRule());
  while (Match(TokenKind::kPipe)) {
    prod.rules.push_back(ParseRsRule());
  }

  Expect(TokenKind::kSemicolon);
  return prod;
}

Stmt* Parser::ParseRandsequenceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRandsequence;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRandsequence);

  // Optional production name: randsequence( [name] )
  Expect(TokenKind::kLParen);
  if (CheckIdentifier()) {
    stmt->rs_top_production = Consume().text;
  }
  Expect(TokenKind::kRParen);

  // Parse one or more rs_production.
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    stmt->rs_productions.push_back(ParseRsProduction());
  }

  Expect(TokenKind::kKwEndsequence);
  stmt->range.end = CurrentLoc();
  return stmt;
}

// --- §19 Covergroup declaration ---

// Skip balanced parentheses. Opening '(' must already be consumed.
static void SkipParenContents(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) ++depth;
    if (lexer.Peek().Is(TokenKind::kRParen)) --depth;
    if (depth > 0) lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kRParen)) lexer.Next();
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

  // Optional extends (§19.3).
  if (Match(TokenKind::kKwExtends)) {
    ExpectIdentifier();
  }

  // Optional port list: ( [tf_port_list] ).
  if (Check(TokenKind::kLParen)) {
    Consume();
    SkipParenContents(lexer_);
  }

  // Optional coverage event.
  if (Match(TokenKind::kAt)) {
    Expect(TokenKind::kLParen);
    ParseEventList();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kAtAt)) {
    Consume();
    Expect(TokenKind::kLParen);
    SkipParenContents(lexer_);
  } else if (Match(TokenKind::kKwWith)) {
    Expect(TokenKind::kKwFunction);
    ExpectIdentifier();
    Expect(TokenKind::kLParen);
    SkipParenContents(lexer_);
  }
  Expect(TokenKind::kSemicolon);

  // Covergroup body — skip (consume to endgroup).
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
