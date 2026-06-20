#include "parser/parser.h"

namespace delta {

ModuleDecl* Parser::ParseCheckerDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind = ModuleDeclKind::kChecker;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwChecker);
  decl->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*decl);

  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    ParseModuleItem(decl->items);
  }
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndchecker);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

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

RsCaseItem Parser::ParseRsCaseItem() {
  RsCaseItem ci;
  if (Match(TokenKind::kKwDefault)) {
    ci.is_default = true;
    Match(TokenKind::kColon);
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

void Parser::ParseRsCodeBlockStmts(std::vector<Stmt*>& stmts) {
  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmts);
    } else {
      stmts.push_back(ParseStmt());
    }
  }
}

RsProd Parser::ParseRsProd() {
  RsProd prod;

  if (Check(TokenKind::kLBrace)) {
    prod.kind = RsProdKind::kCodeBlock;
    Consume();
    ParseRsCodeBlockStmts(prod.code_stmts);
    Expect(TokenKind::kRBrace);
    return prod;
  }

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

  if (Check(TokenKind::kKwRepeat)) {
    prod.kind = RsProdKind::kRepeat;
    Consume();
    Expect(TokenKind::kLParen);
    prod.repeat_count = ParseExpr();
    Expect(TokenKind::kRParen);
    prod.repeat_item = ParseRsProductionItem();
    return prod;
  }

  if (Check(TokenKind::kKwCase)) {
    prod.kind = RsProdKind::kCase;
    Consume();
    Expect(TokenKind::kLParen);
    prod.case_expr = ParseExpr();
    Expect(TokenKind::kRParen);
    bool seen_default = false;
    // 18.17.3: a case production statement shall contain at most one default
    // item; flag any additional default as illegal.
    while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
      auto item_loc = CurrentLoc();
      bool is_default_here = Check(TokenKind::kKwDefault);
      prod.case_items.push_back(ParseRsCaseItem());
      if (is_default_here && seen_default) {
        diag_.Error(item_loc,
                    "case production shall have at most one 'default' item");
      }
      if (is_default_here) seen_default = true;
    }
    Expect(TokenKind::kKwEndcase);
    return prod;
  }

  prod.kind = RsProdKind::kItem;
  prod.item = ParseRsProductionItem();
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
    Expect(TokenKind::kRParen);
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
    Expect(TokenKind::kRParen);
  } else {
    rule.weight = ParsePrimaryExpr();
  }
  if (Check(TokenKind::kLBrace)) {
    Consume();
    ParseRsCodeBlockStmts(rule.weight_code);
    Expect(TokenKind::kRBrace);
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

  // §18.17.7: a production may begin with a data_type_or_void return type. The
  // return type is recognized from a leading 'void', a built-in type keyword,
  // or a leading packed-dimension '['; the parsed type is retained so the
  // value-passing engine can size the production's return value. A production
  // without a return type assumes a void return type (handled downstream).
  if (Check(TokenKind::kKwVoid) || Check(TokenKind::kKwInt) ||
      Check(TokenKind::kKwBit) || Check(TokenKind::kKwLogic) ||
      Check(TokenKind::kKwByte) || Check(TokenKind::kKwShortint) ||
      Check(TokenKind::kKwLongint) || Check(TokenKind::kKwInteger) ||
      Check(TokenKind::kKwString) || Check(TokenKind::kKwReal) ||
      Check(TokenKind::kKwShortreal) || Check(TokenKind::kKwRealtime) ||
      Check(TokenKind::kKwTime) || Check(TokenKind::kLBracket)) {
    prod.return_type = ParseFunctionReturnType();
    prod.has_return_type = true;
  }

  prod.name = ExpectIdentifier().text;

  // §18.17.7: productions that accept data declare a tf_port_list of formal
  // arguments, using the same syntax as a task prototype. Parse and retain the
  // formals so the value-passing engine can bind actual arguments to them.
  if (Check(TokenKind::kLParen)) {
    prod.has_ports = true;
    prod.ports = ParseFunctionArgs(true);
  }

  Expect(TokenKind::kColon);

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

  Expect(TokenKind::kLParen);
  if (CheckIdentifier()) {
    stmt->rs_top_production = Consume().text;
  }
  Expect(TokenKind::kRParen);

  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    stmt->rs_productions.push_back(ParseRsProduction());
  }

  Expect(TokenKind::kKwEndsequence);
  stmt->range.end = CurrentLoc();
  return stmt;
}

static void SkipCoverpointBody(Lexer& lexer) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kLBrace) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kLBrace)) {
    lexer.Next();
    SkipBraceBlock(lexer);
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

void Parser::ParseBlockEventExpression() {
  do {
    if (!Check(TokenKind::kKwBegin) && !Check(TokenKind::kKwEnd)) {
      diag_.Error(CurrentLoc(), "expected 'begin' or 'end' in block event");
      return;
    }
    Consume();
    ExpectIdentifier();
    while (Match(TokenKind::kDot)) {
      ExpectIdentifier();
    }
  } while (Match(TokenKind::kKwOr));
}

// Classify the current token and update the tf_port-style formal-list scan
// state for one step. Shared by ParseCovergroupFormalList and
// ParseSampleFormalList; the per-list behaviors (what to do when a formal name
// is flushed, and which directions to reject) are supplied as callbacks.
// pending_loc is always recorded on the identifier branch; callers that do not
// need it simply ignore the field.
void Parser::StepTfPortFormalScan(
    TfPortFormalScan& st, const std::function<void()>& flush,
    const std::function<bool()>& reject_direction) {
  if (Check(TokenKind::kLParen)) {
    ++st.depth;
  } else if (Check(TokenKind::kRParen)) {
    --st.depth;
    if (st.depth == 0) flush();
  } else if (reject_direction()) {
    // diagnostic emitted; nothing else to record for this token.
  } else if (st.depth == 1 && Check(TokenKind::kComma)) {
    flush();
  } else if (st.depth == 1 && Check(TokenKind::kEq)) {
    // Everything up to the next comma is a default-value expression whose
    // identifiers are not formal-argument names.
    st.in_default = true;
  } else if (!st.in_default && Check(TokenKind::kIdentifier)) {
    st.pending = CurrentToken().text;
    st.pending_loc = CurrentLoc();
    st.have_pending = true;
  }
}

void Parser::ParseCovergroupFormalList(std::vector<std::string>& names) {
  // Scan across the covergroup's optional formal-argument list, which follows
  // the same balanced-parenthesis shape as a tf_port_list. While scanning,
  // reject any formal declared with output or inout direction, which is not
  // permitted for a covergroup formal (LRM 19.3), and collect each formal's
  // name. In a tf_port the declared name is the last identifier that appears
  // before a comma, a default-value '=', or the closing parenthesis.
  TfPortFormalScan st;
  auto flush = [&]() {
    if (st.have_pending) names.emplace_back(st.pending);
    st.have_pending = false;
    st.in_default = false;
  };
  auto reject_output_inout = [&]() {
    if (!Check(TokenKind::kKwOutput) && !Check(TokenKind::kKwInout))
      return false;
    diag_.Error(CurrentLoc(),
                "a covergroup formal argument cannot be declared 'output' "
                "or 'inout'");
    return true;
  };
  while (st.depth > 0 && !AtEnd()) {
    StepTfPortFormalScan(st, flush, reject_output_inout);
    if (st.depth > 0) Consume();
  }
  if (Check(TokenKind::kRParen)) Consume();
}

// §19.8.1: a sample method formal shares the covergroup argument scope, so a
// name appearing in both the covergroup formal list and the sample formal list
// is illegal. Returns true when the pending sample formal name reuses one of
// the covergroup formal-argument names. Free of Parser state so it stays out of
// the caller's cognitive-complexity budget.
static bool ReusesCovergroupFormal(
    const std::vector<std::string>& covergroup_formals,
    std::string_view pending) {
  for (const auto& formal : covergroup_formals) {
    if (formal == pending) return true;
  }
  return false;
}

void Parser::ParseSampleFormalList(
    const std::vector<std::string>& covergroup_formals) {
  // Scan across the formal-argument list of an overridden sample method
  // (introduced by "with function sample"). LRM 19.8.1 places two constraints
  // on these formals that are checked here: a sample formal shall not designate
  // an output direction, and because the sample formals share the covergroup's
  // argument scope (the formals consumed by the covergroup new operator), a
  // name shall not be specified in both the covergroup and sample lists.
  TfPortFormalScan st;
  auto flush = [&]() {
    if (st.have_pending &&
        ReusesCovergroupFormal(covergroup_formals, st.pending)) {
      diag_.Error(st.pending_loc,
                  "sample method formal argument '" + std::string(st.pending) +
                      "' shares the covergroup argument scope and cannot "
                      "reuse a covergroup formal-argument name");
    }
    st.have_pending = false;
    st.in_default = false;
  };
  auto reject_output_inout = [&]() {
    if (!Check(TokenKind::kKwOutput) && !Check(TokenKind::kKwInout))
      return false;
    diag_.Error(CurrentLoc(),
                "a sample method formal argument cannot designate an output "
                "direction");
    return true;
  };
  while (st.depth > 0 && !AtEnd()) {
    StepTfPortFormalScan(st, flush, reject_output_inout);
    if (st.depth > 0) Consume();
  }
  if (Check(TokenKind::kRParen)) Consume();
}

void Parser::ParseCovergroupDecl(std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCovergroupDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCovergroup);

  if (Check(TokenKind::kKwExtends)) {
    // §19.4.1 embedded covergroup inheritance: the derived covergroup is
    // written `covergroup extends base ;` with no fresh name of its own. The
    // covergroup_identifier that follows `extends` names the base covergroup,
    // and the derived covergroup takes that same name so every reference to it
    // resolves to the derived instance.
    Consume();
    auto base = Expect(TokenKind::kIdentifier);
    item->name = base.text;
    item->covergroup_extends_base = base.text;
  } else {
    item->name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kKwExtends)) {
      item->covergroup_extends_base = ExpectIdentifier().text;
    }
  }

  known_types_.insert(item->name);

  std::vector<std::string> covergroup_formals;
  if (Check(TokenKind::kLParen)) {
    Consume();
    ParseCovergroupFormalList(covergroup_formals);
  }

  if (Match(TokenKind::kAt)) {
    Expect(TokenKind::kLParen);
    ParseEventList();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kAtAt)) {
    Consume();
    Expect(TokenKind::kLParen);
    ParseBlockEventExpression();
    Expect(TokenKind::kRParen);
  } else if (Match(TokenKind::kKwWith)) {
    Expect(TokenKind::kKwFunction);
    auto sample_id = ExpectIdentifier();
    if (sample_id.text != "sample") {
      diag_.Error(sample_id.loc, "expected 'sample', got '" +
                                     std::string(sample_id.text) + "'");
    }
    Expect(TokenKind::kLParen);
    ParseSampleFormalList(covergroup_formals);
  }
  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndgroup) && !AtEnd()) {
    SkipCovergroupItem();
  }
  Expect(TokenKind::kKwEndgroup);
  MatchEndLabel(item->name);
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
  if (Check(TokenKind::kIdentifier) && IsOptionKeyword(CurrentToken().text)) {
    SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
    return;
  }

  if (IsCoverpointOrCross(CurrentToken().kind)) {
    Consume();
    SkipCoverpointBody(lexer_);
    return;
  }

  if (Check(TokenKind::kIdentifier)) {
    Consume();
    if (Match(TokenKind::kColon) && IsCoverpointOrCross(CurrentToken().kind)) {
      Consume();
    }
    SkipCoverpointBody(lexer_);
    return;
  }

  SkipToSemiOrEnd(lexer_, TokenKind::kKwEndgroup);
}

}  // namespace delta
