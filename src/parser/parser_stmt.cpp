#include "parser/parser.h"

namespace delta {

// --- Statements (LRM section 12) ---

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

// Helper: check whether the current token starts a data type keyword.
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

Stmt* Parser::ParseStmt() {
  auto attrs = ParseAttributes();

  if (Match(TokenKind::kSemicolon)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kNull;
    stmt->attrs = std::move(attrs);
    return stmt;
  }

  // unique/unique0/priority qualifiers for case/if (LRM section 12.4.2, 12.5)
  auto qual = TokenToCaseQualifier(CurrentToken().kind);
  if (qual != CaseQualifier::kNone) {
    Consume();
  }

  Stmt* stmt = ParseStmtBody();
  if (stmt != nullptr) {
    if (!attrs.empty()) stmt->attrs = std::move(attrs);
    if (qual != CaseQualifier::kNone) stmt->qualifier = qual;
  }
  return stmt;
}

Stmt* Parser::ParseStmtBody() {
  switch (CurrentToken().kind) {
    case TokenKind::kKwBegin:
      return ParseBlockStmt();
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
      return ParseForkStmt();
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
    case TokenKind::kAt:
      return ParseEventControlStmt();
    case TokenKind::kArrow:
      return ParseEventTriggerStmt();
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
    case TokenKind::kKwWaitOrder:
      return ParseWaitOrderStmt();
    case TokenKind::kKwRandcase:
      return ParseRandcaseStmt();
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

// LRM section 9.3.1 -- block_item_declaration detection
bool Parser::IsBlockVarDeclStart() {
  auto tk = CurrentToken().kind;
  if (tk == TokenKind::kKwAutomatic || tk == TokenKind::kKwStatic) {
    return true;  // §6.21 explicit lifetime qualifier
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
  return CurrentToken().Is(TokenKind::kIdentifier) &&
         known_types_.count(CurrentToken().text) != 0;
}

// LRM section 9.3.1 -- block-level variable declarations
void Parser::ParseBlockVarDecls(std::vector<Stmt*>& stmts) {
  bool is_automatic = Match(TokenKind::kKwAutomatic);             // §6.21
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);  // §6.21
  Match(TokenKind::kKwVar);  // optional 'var' prefix (§6.8)
  DataType dtype = ParseDataType();
  do {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kVarDecl;
    s->range.start = CurrentLoc();
    s->var_decl_type = dtype;
    s->var_is_automatic = is_automatic;
    s->var_is_static = is_static;
    s->var_name = ExpectIdentifier().text;
    ParseUnpackedDims(s->var_unpacked_dims);
    if (Match(TokenKind::kEq)) {
      s->var_init = ParseExpr();
    }
    stmts.push_back(s);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

// LRM section 12.6 / section 9.3.4 -- named blocks
Stmt* Parser::ParseBlockStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin);
  // Optional block label: ": label_name"
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
  // Optional end label: ": label_name"
  if (Match(TokenKind::kColon)) {
    ExpectIdentifier();
  }
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

// LRM section 12.5 -- case / casex / casez / case inside
Stmt* Parser::ParseCaseStmt(TokenKind case_kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = case_kind;
  stmt->range.start = CurrentLoc();
  Consume();  // case/casex/casez
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  // LRM section 12.5.4 -- "case (expr) inside"
  if (Match(TokenKind::kKwInside)) {
    stmt->case_inside = true;
  }
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    stmt->case_items.push_back(ParseCaseItem());
  }
  Expect(TokenKind::kKwEndcase);
  return stmt;
}

CaseItem Parser::ParseCaseItem() {
  CaseItem item;
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
  } else {
    item.patterns.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      item.patterns.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kColon);
  item.body = ParseStmt();
  return item;
}

// LRM section 12.7.1 -- for with optional variable declaration in init
Stmt* Parser::ParseForStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFor;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFor);
  Expect(TokenKind::kLParen);
  // Check for variable declaration: "for (int i = 0; ...)"
  if (IsDataTypeKeyword(CurrentToken().kind)) {
    stmt->for_init_type = ParseDataType();
    stmt->for_init = ParseAssignmentOrExprStmt();
  } else {
    stmt->for_init = ParseAssignmentOrExprStmt();
  }
  stmt->for_cond = ParseExpr();
  Expect(TokenKind::kSemicolon);
  stmt->for_step = ParseAssignmentOrExprNoSemi();
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

// LRM section 12.6 / section 9.3.2 -- fork-join with optional labels
Stmt* Parser::ParseForkStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFork;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFork);
  // Optional fork label: ": label_name"
  if (Match(TokenKind::kColon)) {
    stmt->label = ExpectIdentifier().text;
  }
  while (!Check(TokenKind::kKwJoin) && !Check(TokenKind::kKwJoinAny) &&
         !Check(TokenKind::kKwJoinNone) && !AtEnd()) {
    auto* s = ParseStmt();
    if (s != nullptr) {
      stmt->fork_stmts.push_back(s);
    }
  }
  stmt->join_kind = CurrentToken().kind;
  Consume();  // join / join_any / join_none
  // Optional end label: ": label_name"
  if (Match(TokenKind::kColon)) {
    ExpectIdentifier();
  }
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

// Parse a simple or hierarchical identifier for foreach array.
// Stops before '[' so that the loop variable list is not consumed.
Expr* Parser::ParseForeachArrayId() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->range.start = CurrentLoc();
  expr->text = ExpectIdentifier().text;
  // Handle hierarchical names: a.b.c
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

// LRM section 12.7.3 -- foreach loop
// Syntax: foreach ( ps_or_hierarchical_array_identifier [ loop_vars ] ) stmt
// The array id may be hierarchical (a.b.c); loop vars are comma-separated
// identifiers where some slots may be empty.
Stmt* Parser::ParseForeachStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForeach);
  Expect(TokenKind::kLParen);
  // Parse the array name without consuming the [loop_vars] as a subscript.
  stmt->expr = ParseForeachArrayId();
  Expect(TokenKind::kLBracket);
  ParseForeachVars(stmt->foreach_vars);
  Expect(TokenKind::kRBracket);
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

void Parser::ParseForeachVars(std::vector<std::string_view>& vars) {
  // First variable (may be empty)
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
  // wait fork; (§9.6.1)
  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kWaitFork;
    Expect(TokenKind::kSemicolon);
    return stmt;
  }
  // wait (expr) stmt
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
  // disable fork; (§9.6.3)
  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kDisableFork;
    Expect(TokenKind::kSemicolon);
    return stmt;
  }
  // disable block_name;
  stmt->kind = StmtKind::kDisable;
  stmt->expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

// Returns true if the token is a compound assignment operator (§11.4.1).
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

// Parse optional intra-assignment timing control on the RHS of an
// assignment (§10.4.1 delay, §10.4.2 event, §9.4.5 repeat), then
// parse the RHS expression.
void Parser::ParseIntraAssignTiming(Stmt* stmt) {
  if (Check(TokenKind::kHash)) {
    // Intra-assignment delay: a = #10 b;
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      stmt->delay = ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      stmt->delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kAt)) {
    // Intra-assignment event: a = @(posedge clk) b;
    Consume();
    Expect(TokenKind::kLParen);
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kKwRepeat)) {
    // repeat(N) @(event_list) (§9.4.5)
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
  // Parse prefix/primary first -- stop before infix operators so that
  // '<=' is available for nonblocking assignment detection.
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
    // Compound assignment operators (§11.4.1): a += b, a <<= b, etc.
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    auto op_tok = Consume();
    stmt->rhs = ParseExpr();
    stmt->delay = nullptr;
    // Store the compound op in the rhs as a binary with the original op.
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op_tok.kind;
    bin->lhs = lhs_expr;
    bin->rhs = stmt->rhs;
    bin->range.start = lhs_expr->range.start;
    stmt->rhs = bin;
  } else {
    // Not an assignment -- complete the expression via infix parsing.
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

Stmt* Parser::ParseDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHash);
  // Parenthesized delay may contain min:typ:max (§11.11).
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
    // @* -- implicit sensitivity (§9.4.2.2)
    stmt->is_star_event = true;
  } else if (Check(TokenKind::kLParen)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      // @(*) -- implicit sensitivity (§9.4.2.2)
      stmt->is_star_event = true;
    } else {
      stmt->events = ParseEventList();
    }
    Expect(TokenKind::kRParen);
  } else {
    // @ev -- named event or bare signal shorthand.
    EventExpr ev;
    ev.signal = ParseExpr();
    stmt->events.push_back(ev);
  }
  stmt->body = ParseStmt();
  return stmt;
}

// LRM §10.6.1 -- procedural continuous assign: assign lhs = rhs;
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

// LRM §10.6.1 -- procedural deassign: deassign lhs;
Stmt* Parser::ParseProceduralDeassignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDeassign);
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

// LRM §10.6.2 -- force: force lhs = rhs;
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

// LRM §10.6.2 -- release: release lhs;
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
