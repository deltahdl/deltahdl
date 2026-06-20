#include "parser/parser.h"

namespace delta {

static bool IsDataTypeKeyword(TokenKind tk);

// CPD-dedup: a label preceding begin/fork is equivalent to a block name, so the
// matching name after end/join* may be the inline name or that prefix label.
// Validates the optional trailing ": name" against the effective block name.
struct ParserStmtHelpers {
  static void MatchEndBlockLabel(Parser& p, std::string_view inline_label,
                                 std::string_view prefix_label) {
    std::string_view block_name =
        inline_label.empty() ? prefix_label : inline_label;
    if (p.Match(TokenKind::kColon)) {
      auto end_id = p.ExpectIdentifier();
      if (block_name.empty()) {
        p.diag_.Error(end_id.loc, "end label '" + std::string(end_id.text) +
                                      "' specified for unnamed block");
      } else if (end_id.text != block_name) {
        p.diag_.Error(end_id.loc, "end label '" + std::string(end_id.text) +
                                      "' does not match block name '" +
                                      std::string(block_name) + "'");
      }
    }
  }

  static void ApplyStmtLabel(Parser& p, Stmt* stmt,
                             std::string_view prefix_label) {
    if (!prefix_label.empty() && stmt->label.empty()) {
      stmt->label = prefix_label;
    } else if (!prefix_label.empty() && !stmt->label.empty()) {
      p.diag_.Error(stmt->range.start,
                    "cannot have both a statement label and a block name");
    }
  }

  static void CheckQualifiedElseIfBranches(Parser& p, Stmt* stmt) {
    for (Stmt* cur = stmt->else_branch; cur && cur->kind == StmtKind::kIf;
         cur = cur->else_branch) {
      if (cur->qualifier != CaseQualifier::kNone) {
        p.diag_.Error(cur->range.start,
                      "unique, unique0, or priority cannot appear on an "
                      "else-if branch; wrap the nested if in begin-end");
        break;
      }
    }
  }

  static void ApplyStmtQualifierAndAttrs(Parser& p, Stmt* stmt,
                                         CaseQualifier qual,
                                         std::vector<Attribute>& attrs) {
    if (!attrs.empty()) stmt->attrs = std::move(attrs);
    if (qual != CaseQualifier::kNone) stmt->qualifier = qual;
    if (qual != CaseQualifier::kNone && stmt->kind == StmtKind::kIf) {
      CheckQualifiedElseIfBranches(p, stmt);
    }
  }

  static void ParseForLocalDeclInits(Parser& p, Stmt* stmt) {
    do {
      p.Match(TokenKind::kKwVar);
      stmt->for_init_types.push_back(p.ParseDataType());
      stmt->for_inits.push_back(p.ParseAssignmentOrExprNoSemi());
    } while (p.Match(TokenKind::kComma));
    p.Expect(TokenKind::kSemicolon);
  }

  static void ParseForPlainInits(Parser& p, Stmt* stmt) {
    do {
      if (p.Check(TokenKind::kKwVar) ||
          IsDataTypeKeyword(p.CurrentToken().kind)) {
        // The first control variable was a plain assignment, so a later item
        // attempting a local declaration mixes declared and non-declared
        // control variables, which is not allowed.
        p.diag_.Error(
            p.CurrentLoc(),
            "for-loop initialization shall declare either all or none "
            "of its control variables locally");
        p.Match(TokenKind::kKwVar);
        stmt->for_init_types.push_back(p.ParseDataType());
        stmt->for_inits.push_back(p.ParseAssignmentOrExprNoSemi());
      } else {
        stmt->for_init_types.emplace_back();
        stmt->for_inits.push_back(p.ParseAssignmentOrExprNoSemi());
      }
    } while (p.Match(TokenKind::kComma));
    p.Expect(TokenKind::kSemicolon);
  }
};

static CaseQualifier TokenToCaseQualifier(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwUnique:
      return CaseQualifier::kUnique;
    case TokenKind::kKwUnique0:
      return CaseQualifier::kUnique0;
    case TokenKind::kKwPriority:
      return CaseQualifier::kPriority;
    default:
      return CaseQualifier::kNone;
  }
}

static bool IsDataTypeKeyword(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwLogic:
    case TokenKind::kKwReg:
    case TokenKind::kKwBit:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwInt:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwReal:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwRealtime:
    case TokenKind::kKwTime:
    case TokenKind::kKwString:
      return true;
    default:
      return false;
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

Stmt* Parser::ParseStmt() {
  auto prefix_label = TryParseStmtLabel();
  auto attrs = ParseAttributes();

  if (Match(TokenKind::kSemicolon)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kNull;
    stmt->label = prefix_label;
    stmt->attrs = std::move(attrs);
    return stmt;
  }

  auto qual = TokenToCaseQualifier(CurrentToken().kind);
  if (qual != CaseQualifier::kNone) {
    Consume();
  }

  Stmt* stmt = ParseStmtBody(prefix_label);
  if (stmt != nullptr) {
    ParserStmtHelpers::ApplyStmtLabel(*this, stmt, prefix_label);
    ParserStmtHelpers::ApplyStmtQualifierAndAttrs(*this, stmt, qual, attrs);
  }
  return stmt;
}

Stmt* Parser::ParseStmtBody(std::string_view prefix_label) {
  switch (CurrentToken().kind) {
    case TokenKind::kKwBegin:
      return ParseBlockStmt(prefix_label);
    case TokenKind::kKwIf:
      return ParseIfStmt();
    case TokenKind::kKwCase:
    case TokenKind::kKwCasex:
    case TokenKind::kKwCasez:
      return ParseCaseStmt(CurrentToken().kind);
    case TokenKind::kKwFor:
      return ParseForStmt();
    case TokenKind::kKwForeach:
      return ParseForeachStmt();
    case TokenKind::kKwWhile:
      return ParseWhileStmt();
    case TokenKind::kKwForever:
      return ParseForeverStmt();
    case TokenKind::kKwRepeat:
      return ParseRepeatStmt();
    case TokenKind::kKwFork:
      return ParseForkStmt(prefix_label);
    case TokenKind::kKwDo:
      return ParseDoWhileStmt();
    case TokenKind::kKwBreak:
      return ParseSimpleKeywordStmt(StmtKind::kBreak);
    case TokenKind::kKwContinue:
      return ParseSimpleKeywordStmt(StmtKind::kContinue);
    case TokenKind::kKwReturn:
      return ParseReturnStmt();
    case TokenKind::kKwWait:
      return ParseWaitStmt();
    case TokenKind::kKwDisable:
      return ParseDisableStmt();
    case TokenKind::kHash:
      return ParseDelayStmt();
    case TokenKind::kHashHash:
      return ParseCycleDelayStmt();
    case TokenKind::kAt:
      return ParseEventControlStmt();
    case TokenKind::kArrow:
      return ParseEventTriggerStmt();
    case TokenKind::kDashGtGt:
      return ParseNbEventTriggerStmt();
    case TokenKind::kKwAssign:
      return ParseProceduralAssignStmt();
    case TokenKind::kKwDeassign:
      return ParseProceduralDeassignStmt();
    case TokenKind::kKwForce:
      return ParseForceStmt();
    case TokenKind::kKwRelease:
      return ParseReleaseStmt();
    case TokenKind::kKwAssert:
      return ParseImmediateAssert();
    case TokenKind::kKwAssume:
      return ParseImmediateAssume();
    case TokenKind::kKwCover:
      return ParseImmediateCover();
    case TokenKind::kKwRestrict:

      diag_.Error(CurrentLoc(),
                  "restrict has no immediate (procedural) form per §16.2; "
                  "use `restrict property (...)` at module-item level");
      Consume();
      return arena_.Create<Stmt>();
    case TokenKind::kKwWaitOrder:
      return ParseWaitOrderStmt();
    case TokenKind::kKwRandcase:
      return ParseRandcaseStmt();
    case TokenKind::kKwRandsequence:
      return ParseRandsequenceStmt();
    case TokenKind::kKwExpect:
      return ParseExpectStmt();
    default:
      return ParseAssignmentOrExprStmt();
  }
}

Stmt* Parser::ParseEventTriggerStmt() {
  auto* s = arena_.Create<Stmt>();
  s->kind = StmtKind::kEventTrigger;
  s->range.start = CurrentLoc();
  Consume();
  s->expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return s;
}

Stmt* Parser::ParseNbEventTriggerStmt() {
  auto* s = arena_.Create<Stmt>();
  s->kind = StmtKind::kNbEventTrigger;
  s->range.start = CurrentLoc();
  Consume();

  // delay_or_event_control = delay_control | event_control
  //                       | repeat ( expression ) event_control
  if (Check(TokenKind::kHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      s->delay = ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      s->delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kKwRepeat)) {
    Consume();
    Expect(TokenKind::kLParen);
    s->repeat_event_count = ParseExpr();
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kAt);
    Expect(TokenKind::kLParen);
    s->events = ParseEventList();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kAt)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      s->is_star_event = true;
    } else if (Check(TokenKind::kLParen)) {
      Consume();
      if (Match(TokenKind::kStar)) {
        s->is_star_event = true;
      } else {
        s->events = ParseEventList();
      }
      Expect(TokenKind::kRParen);
    } else {
      EventExpr ev;
      ev.signal = ParseExpr();
      s->events.push_back(ev);
    }
  }
  s->expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return s;
}

bool Parser::IsBlockVarDeclStart() {
  auto saved = lexer_.SavePos();
  while (Check(TokenKind::kAttrStart)) {
    Consume();
    int depth = 1;
    while (depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kAttrEnd)) depth--;
      Consume();
    }
  }
  bool result = IsBlockVarDeclStartCore();
  lexer_.RestorePos(saved);
  return result;
}

bool Parser::IsBlockVarDeclStartCore() {
  auto tk = CurrentToken().kind;
  if (tk == TokenKind::kKwAutomatic || tk == TokenKind::kKwStatic) {
    return true;
  }
  if (tk == TokenKind::kKwParameter || tk == TokenKind::kKwLocalparam) {
    return true;
  }
  if (tk == TokenKind::kKwConst) {
    return true;
  }
  if (tk == TokenKind::kKwTypedef) {
    return true;
  }
  if (tk == TokenKind::kKwImport) {
    return true;
  }
  if (tk == TokenKind::kKwLet) {
    return true;
  }
  if (tk == TokenKind::kKwStruct || tk == TokenKind::kKwUnion ||
      tk == TokenKind::kKwEnum || tk == TokenKind::kKwVar) {
    return true;
  }
  if (IsDataTypeKeyword(tk)) {
    auto saved = lexer_.SavePos();
    Consume();
    bool is_decl = CheckIdentifier() || Check(TokenKind::kKwSigned) ||
                   Check(TokenKind::kKwUnsigned) || Check(TokenKind::kLBracket);
    lexer_.RestorePos(saved);
    return is_decl;
  }
  return Check(TokenKind::kIdentifier) &&
         known_types_.count(CurrentToken().text) != 0;
}

void Parser::ParseBlockDataDecl(std::vector<Stmt*>& stmts,
                                const std::vector<Attribute>& attrs) {
  bool is_const = Match(TokenKind::kKwConst);
  bool is_automatic = Match(TokenKind::kKwAutomatic);
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);
  bool saw_var = Match(TokenKind::kKwVar);
  if (!is_automatic && !is_static && saw_var) {
    is_automatic = Match(TokenKind::kKwAutomatic);
    is_static = !is_automatic && Match(TokenKind::kKwStatic);
  }
  DataType dtype = ParseDataType();
  if (saw_var && dtype.kind == DataTypeKind::kImplicit &&
      Check(TokenKind::kLBracket)) {
    ParsePackedDims(dtype);
  }

  if (!saw_var && dtype.kind == DataTypeKind::kImplicit) {
    diag_.Error(CurrentLoc(),
                "data_declaration without an explicit data type requires "
                "the 'var' keyword");
  }
  do {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kVarDecl;
    s->range.start = CurrentLoc();
    s->var_decl_type = dtype;
    s->var_is_const = is_const;
    s->var_is_automatic = is_automatic;
    s->var_is_static = is_static;
    s->var_name = ExpectIdentifier().text;
    s->attrs = attrs;
    ParseUnpackedDims(s->var_unpacked_dims);
    if (Match(TokenKind::kEq)) {
      s->var_init = ParseExpr();
    }
    stmts.push_back(s);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseBlockVarDecls(std::vector<Stmt*>& stmts) {
  auto attrs = ParseAttributes();

  if (Check(TokenKind::kKwLet)) {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kBlockItemDecl;
    s->range.start = CurrentLoc();
    s->decl_item = ParseLetDecl();
    s->attrs = std::move(attrs);
    stmts.push_back(s);
    return;
  }

  if (Check(TokenKind::kKwTypedef)) {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kBlockItemDecl;
    s->range.start = CurrentLoc();
    s->decl_item = ParseTypedef();
    s->attrs = std::move(attrs);
    stmts.push_back(s);
    return;
  }

  if (Check(TokenKind::kKwImport)) {
    std::vector<ModuleItem*> import_items;
    ParseImportDecl(import_items);
    for (auto* imp : import_items) {
      auto* s = arena_.Create<Stmt>();
      s->kind = StmtKind::kBlockItemDecl;
      s->range.start = imp->loc;
      s->decl_item = imp;
      s->attrs = attrs;
      stmts.push_back(s);
    }
    return;
  }

  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    std::vector<ModuleItem*> param_items;
    ParseParamDecl(param_items);
    for (auto* param : param_items) {
      auto* s = arena_.Create<Stmt>();
      s->kind = StmtKind::kVarDecl;
      s->range.start = param->loc;
      s->var_decl_type = param->data_type;
      s->var_name = param->name;
      s->var_init = param->init_expr;
      s->attrs = attrs;
      stmts.push_back(s);
    }
    return;
  }
  ParseBlockDataDecl(stmts, attrs);
}

Stmt* Parser::ParseBlockStmt(std::string_view prefix_label) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin);

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier().text;
  }
  while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmt->stmts);
    } else {
      auto* s = ParseStmt();
      if (s != nullptr) {
        stmt->stmts.push_back(s);
      }
    }
  }
  Expect(TokenKind::kKwEnd);

  ParserStmtHelpers::MatchEndBlockLabel(*this, stmt->label, prefix_label);
  stmt->range.end = CurrentLoc();
  return stmt;
}

Stmt* Parser::ParseIfStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwIf);
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  stmt->then_branch = ParseStmt();
  if (Match(TokenKind::kKwElse)) {
    stmt->else_branch = ParseStmt();
  }
  return stmt;
}

Stmt* Parser::ParseCaseStmt(TokenKind case_kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = case_kind;
  stmt->range.start = CurrentLoc();
  Consume();
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);

  if (Check(TokenKind::kKwInside)) {
    auto inside_loc = CurrentLoc();
    Consume();
    if (case_kind != TokenKind::kKwCase) {
      diag_.Error(inside_loc, "'inside' is only valid with 'case'");
    }
    stmt->case_inside = true;
  }

  if (Check(TokenKind::kKwMatches)) {
    auto matches_loc = CurrentLoc();
    Consume();
    if (stmt->case_inside) {
      diag_.Error(matches_loc,
                  "'matches' and 'inside' cannot be used together");
    }
    stmt->case_matches = true;
  }
  bool seen_default = false;
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    auto item_loc = CurrentLoc();
    bool is_default_here = Check(TokenKind::kKwDefault);
    stmt->case_items.push_back(ParseCaseItem(stmt->case_inside));
    if (is_default_here) {
      if (seen_default) {
        diag_.Error(item_loc,
                    "case statement shall have at most one 'default' item");
      }
      seen_default = true;
    }
  }
  Expect(TokenKind::kKwEndcase);
  return stmt;
}

CaseItem Parser::ParseCaseItem(bool inside) {
  CaseItem item;
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
    Match(TokenKind::kColon);
  } else {
    item.patterns.push_back(inside ? ParseInsideValueRange() : ParseExpr());
    while (Match(TokenKind::kComma)) {
      item.patterns.push_back(inside ? ParseInsideValueRange() : ParseExpr());
    }
    Expect(TokenKind::kColon);
  }
  item.body = ParseStmt();
  return item;
}

Stmt* Parser::ParseForStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFor;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFor);
  Expect(TokenKind::kLParen);

  if (Check(TokenKind::kSemicolon)) {
    Consume();
  } else if (Check(TokenKind::kKwVar) ||
             IsDataTypeKeyword(CurrentToken().kind)) {
    ParserStmtHelpers::ParseForLocalDeclInits(*this, stmt);
  } else {
    ParserStmtHelpers::ParseForPlainInits(*this, stmt);
  }

  if (!Check(TokenKind::kSemicolon)) {
    stmt->for_cond = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);

  if (!Check(TokenKind::kRParen)) {
    do {
      stmt->for_steps.push_back(ParseAssignmentOrExprNoSemi());
    } while (Match(TokenKind::kComma));
  }
  Expect(TokenKind::kRParen);
  stmt->for_body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseWhileStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kWhile;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWhile);
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseForeverStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForever;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForever);
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseRepeatStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRepeat;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRepeat);
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseForkStmt(std::string_view prefix_label) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFork;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFork);

  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier().text;
  }
  while (!Check(TokenKind::kKwJoin) && !Check(TokenKind::kKwJoinAny) &&
         !Check(TokenKind::kKwJoinNone) && !AtEnd()) {
    if (IsBlockVarDeclStart()) {
      ParseBlockVarDecls(stmt->fork_stmts);
    } else {
      auto* s = ParseStmt();
      if (s != nullptr) stmt->fork_stmts.push_back(s);
    }
  }
  stmt->join_kind = CurrentToken().kind;
  Consume();

  ParserStmtHelpers::MatchEndBlockLabel(*this, stmt->label, prefix_label);
  return stmt;
}

Stmt* Parser::ParseSimpleKeywordStmt(StmtKind kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Consume();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseReturnStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kReturn;
  stmt->range.start = CurrentLoc();
  Consume();
  if (!Check(TokenKind::kSemicolon)) {
    stmt->expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Expr* Parser::ParseForeachArrayId() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->range.start = CurrentLoc();
  expr->text = ExpectIdentifier().text;

  while (Check(TokenKind::kDot) && !AtEnd()) {
    Consume();
    auto* mem = arena_.Create<Expr>();
    mem->kind = ExprKind::kMemberAccess;
    mem->lhs = expr;
    mem->text = ExpectIdentifier().text;
    expr = mem;
  }
  return expr;
}

Stmt* Parser::ParseForeachStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForeach);
  Expect(TokenKind::kLParen);

  stmt->expr = ParseForeachArrayId();
  Expect(TokenKind::kLBracket);
  ParseForeachVars(stmt->foreach_vars);
  Expect(TokenKind::kRBracket);
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

void Parser::ParseForeachVars(std::vector<std::string_view>& vars) {
  if (CheckIdentifier()) {
    vars.push_back(Consume().text);
  } else {
    vars.emplace_back();
  }
  while (Match(TokenKind::kComma)) {
    if (CheckIdentifier()) {
      vars.push_back(Consume().text);
    } else {
      vars.emplace_back();
    }
  }
}

Stmt* Parser::ParseDoWhileStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDoWhile;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDo);
  stmt->body = ParseStmt();
  Expect(TokenKind::kKwWhile);
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseWaitStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWait);

  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kWaitFork;
    Expect(TokenKind::kSemicolon);
    return stmt;
  }

  stmt->kind = StmtKind::kWait;
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseDisableStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDisable);

  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kDisableFork;
    Expect(TokenKind::kSemicolon);
    return stmt;
  }

  stmt->kind = StmtKind::kDisable;
  stmt->expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

static bool IsCompoundAssignOp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Parser::ParseIntraAssignTiming(Stmt* stmt) {
  if (Check(TokenKind::kHashHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      stmt->cycle_delay = ParseExpr();
      Expect(TokenKind::kRParen);
    } else {
      stmt->cycle_delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      stmt->delay = ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      stmt->delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kAt)) {
    Consume();
    Expect(TokenKind::kLParen);
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kKwRepeat)) {
    Consume();
    Expect(TokenKind::kLParen);
    stmt->repeat_event_count = ParseExpr();
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kAt);
    Expect(TokenKind::kLParen);
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen);
  }
  stmt->rhs = ParseExpr();
}

Stmt* Parser::ParseAssignmentOrExprNoSemi() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();

  auto* lhs_expr = ParsePrefixExpr();

  if (Match(TokenKind::kEq)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    ParseIntraAssignTiming(stmt);
  } else if (Match(TokenKind::kLtEq)) {
    stmt->kind = StmtKind::kNonblockingAssign;
    stmt->lhs = lhs_expr;
    ParseIntraAssignTiming(stmt);
  } else if (IsCompoundAssignOp(CurrentToken().kind)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    auto op_tok = Consume();
    stmt->rhs = ParseExpr();
    stmt->delay = nullptr;

    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op_tok.kind;
    bin->lhs = lhs_expr;
    bin->rhs = stmt->rhs;
    bin->range.start = lhs_expr->range.start;
    stmt->rhs = bin;
  } else {
    stmt->kind = StmtKind::kExprStmt;
    stmt->expr = ParseInfixBp(lhs_expr, 0);
  }
  return stmt;
}

Stmt* Parser::ParseAssignmentOrExprStmt() {
  auto* stmt = ParseAssignmentOrExprNoSemi();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseCycleDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCycleDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHashHash);
  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->cycle_delay = ParseExpr();
    Expect(TokenKind::kRParen);
  } else {
    stmt->cycle_delay = ParsePrimaryExpr();
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHash);

  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->delay = ParseMinTypMaxExpr();
    Expect(TokenKind::kRParen);
  } else {
    stmt->delay = ParsePrimaryExpr();
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseEventControlStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kEventControl;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kAt);
  if (Match(TokenKind::kStar)) {
    stmt->is_star_event = true;
  } else if (Check(TokenKind::kLParen)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      stmt->is_star_event = true;
    } else {
      stmt->events = ParseEventList();
    }
    Expect(TokenKind::kRParen);
  } else {
    EventExpr ev;
    ev.signal = ParseExpr();
    stmt->events.push_back(ev);
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseProceduralAssignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwAssign);
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kEq);
  stmt->rhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseProceduralDeassignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDeassign);
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseForceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForce);
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kEq);
  stmt->rhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseReleaseStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRelease);
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

}  // namespace delta
