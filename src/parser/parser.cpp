#include "parser/parser.h"

#include <optional>

namespace delta {

Parser::Parser(Lexer& lexer, Arena& arena, DiagEngine& diag)
    : lexer_(lexer), arena_(arena), diag_(diag) {}

Token Parser::CurrentToken() { return lexer_.Peek(); }
bool Parser::Check(TokenKind kind) { return CurrentToken().Is(kind); }
bool Parser::AtEnd() { return Check(TokenKind::kEof); }
SourceLoc Parser::CurrentLoc() { return CurrentToken().loc; }

Token Parser::Consume() { return lexer_.Next(); }

bool Parser::Match(TokenKind kind) {
  if (!Check(kind)) {
    return false;
  }
  Consume();
  return true;
}

Token Parser::Expect(TokenKind kind) {
  if (Check(kind)) {
    return Consume();
  }
  auto tok = CurrentToken();
  diag_.Error(tok.loc, "expected " + std::string(TokenKindName(kind)) +
                           ", got " + std::string(TokenKindName(tok.kind)));
  return tok;
}

void Parser::Synchronize() {
  while (!AtEnd()) {
    if (Check(TokenKind::kSemicolon)) {
      Consume();
      return;
    }
    if (Check(TokenKind::kKwEndmodule) || Check(TokenKind::kKwEnd)) {
      return;
    }
    Consume();
  }
}

// --- Top level ---

CompilationUnit* Parser::Parse() {
  auto* unit = arena_.Create<CompilationUnit>();
  while (!AtEnd()) {
    if (!Check(TokenKind::kKwModule)) {
      diag_.Error(CurrentLoc(), "expected module declaration");
      Consume();
      continue;
    }
    auto* mod = ParseModuleDecl();
    if (mod != nullptr) {
      unit->modules.push_back(mod);
    }
  }
  return unit;
}

// --- Module parsing ---

ModuleDecl* Parser::ParseModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwModule);

  auto name_tok = Expect(TokenKind::kIdentifier);
  mod->name = name_tok.text;
  mod->range.start = loc;

  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      ParseParamPortDecl(*mod);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(*mod);
      }
    }
    Expect(TokenKind::kRParen);
  }

  if (Check(TokenKind::kLParen)) {
    ParsePortList(*mod);
  }

  Expect(TokenKind::kSemicolon);
  ParseModuleBody(*mod);
  Expect(TokenKind::kKwEndmodule);
  mod->range.end = CurrentLoc();
  return mod;
}

void Parser::ParseParamPortDecl(ModuleDecl& mod) {
  Match(TokenKind::kKwParameter);
  ParseDataType();  // consume optional type (not stored in params)
  auto name = Expect(TokenKind::kIdentifier);
  Expr* default_val = nullptr;
  if (Match(TokenKind::kEq)) {
    default_val = ParseExpr();
  }
  mod.params.push_back({name.text, default_val});
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }
  mod.ports.push_back(ParsePortDecl());
  while (Match(TokenKind::kComma)) {
    mod.ports.push_back(ParsePortDecl());
  }
  Expect(TokenKind::kRParen);
}

PortDecl Parser::ParsePortDecl() {
  PortDecl port;
  port.loc = CurrentLoc();

  if (Check(TokenKind::kKwInput)) {
    port.direction = Direction::kInput;
    Consume();
  } else if (Check(TokenKind::kKwOutput)) {
    port.direction = Direction::kOutput;
    Consume();
  } else if (Check(TokenKind::kKwInout)) {
    port.direction = Direction::kInout;
    Consume();
  } else if (Check(TokenKind::kKwRef)) {
    port.direction = Direction::kRef;
    Consume();
  }

  port.data_type = ParseDataType();

  auto name_tok = Expect(TokenKind::kIdentifier);
  port.name = name_tok.text;

  if (Match(TokenKind::kEq)) {
    port.default_value = ParseExpr();
  }
  return port;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    ParseModuleItem(mod.items);
  }
}

static std::optional<AlwaysKind> TokenToAlwaysKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwAlways:
      return AlwaysKind::kAlways;
    case TokenKind::kKwAlwaysComb:
      return AlwaysKind::kAlwaysComb;
    case TokenKind::kKwAlwaysFF:
      return AlwaysKind::kAlwaysFF;
    case TokenKind::kKwAlwaysLatch:
      return AlwaysKind::kAlwaysLatch;
    default:
      return std::nullopt;
  }
}

void Parser::ParseModuleItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwTypedef)) {
    items.push_back(ParseTypedef());
    return;
  }
  if (Check(TokenKind::kKwFunction)) {
    items.push_back(ParseFunctionDecl());
    return;
  }
  if (Check(TokenKind::kKwTask)) {
    items.push_back(ParseTaskDecl());
    return;
  }
  if (Check(TokenKind::kKwAssign)) {
    items.push_back(ParseContinuousAssign());
    return;
  }
  if (Check(TokenKind::kKwInitial)) {
    items.push_back(ParseInitialBlock());
    return;
  }
  if (Check(TokenKind::kKwFinal)) {
    items.push_back(ParseFinalBlock());
    return;
  }
  auto ak = TokenToAlwaysKind(CurrentToken().kind);
  if (ak) {
    items.push_back(ParseAlwaysBlock(*ak));
    return;
  }
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    items.push_back(ParseParamDecl());
    return;
  }

  if (Check(TokenKind::kKwEnum)) {
    auto dtype = ParseEnumType();
    ParseVarDeclList(items, dtype);
    return;
  }

  auto dtype = ParseDataType();
  if (dtype.kind != DataTypeKind::kImplicit) {
    ParseVarDeclList(items, dtype);
    return;
  }
  if (!Check(TokenKind::kIdentifier)) {
    diag_.Error(CurrentLoc(), "unexpected token in module body");
    Synchronize();
    return;
  }
  ParseImplicitTypeOrInst(items);
}

void Parser::ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items) {
  auto name_tok = Consume();
  if (known_types_.count(name_tok.text) != 0) {
    DataType dtype;
    dtype.kind = DataTypeKind::kNamed;
    dtype.type_name = name_tok.text;
    ParseVarDeclList(items, dtype);
    return;
  }
  if (Check(TokenKind::kIdentifier) || Check(TokenKind::kHash)) {
    items.push_back(ParseModuleInst(name_tok));
    return;
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = name_tok.loc;
  item->name = name_tok.text;
  if (Match(TokenKind::kEq)) {
    item->init_expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);
  items.push_back(item);
}

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->data_type = dtype;
    item->name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kEq)) {
      item->init_expr = ParseExpr();
    }
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseModuleInst(const Token& module_tok) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kModuleInst;
  item->loc = module_tok.loc;
  item->inst_module = module_tok.text;
  if (Match(TokenKind::kHash)) {
    ParseParenList(item->inst_params);
  }
  item->inst_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    ParsePortConnection(item);
    while (Match(TokenKind::kComma)) {
      ParsePortConnection(item);
    }
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return item;
}

void Parser::ParseParenList(std::vector<Expr*>& out) {
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    out.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      out.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParsePortConnection(ModuleItem* item) {
  if (Match(TokenKind::kDot)) {
    auto name = Expect(TokenKind::kIdentifier);
    Expect(TokenKind::kLParen);
    auto* expr = ParseExpr();
    Expect(TokenKind::kRParen);
    item->inst_ports.push_back({name.text, expr});
  } else {
    item->inst_ports.push_back({{}, ParseExpr()});
  }
}

ModuleItem* Parser::ParseContinuousAssign() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kContAssign;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwAssign);
  item->assign_lhs = ParseExpr();
  Expect(TokenKind::kEq);
  item->assign_rhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseParamDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kParamDecl;
  item->loc = CurrentLoc();
  Consume();  // parameter or localparam
  item->data_type = ParseDataType();
  auto name_tok = Expect(TokenKind::kIdentifier);
  item->name = name_tok.text;
  if (Match(TokenKind::kEq)) {
    item->init_expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseAlwaysBlock(AlwaysKind kind) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAlwaysBlock;
  item->always_kind = kind;
  item->loc = CurrentLoc();
  Consume();  // always / always_comb / always_ff / always_latch

  if (Check(TokenKind::kAt)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      item->sensitivity = ParseEventList();
      Expect(TokenKind::kRParen);
    } else if (Check(TokenKind::kStar)) {
      Consume();  // @*
    }
  }

  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseInitialBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kInitialBlock;
  item->loc = CurrentLoc();
  Consume();  // initial
  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseFinalBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFinalBlock;
  item->loc = CurrentLoc();
  Consume();  // final
  item->body = ParseStmt();
  return item;
}

// --- Statements ---

Stmt* Parser::ParseStmt() {
  if (Match(TokenKind::kSemicolon)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kNull;
    return stmt;
  }

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
    default:
      return ParseAssignmentOrExprStmt();
  }
}

Stmt* Parser::ParseBlockStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kBlock;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwBegin);
  while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
    auto* s = ParseStmt();
    if (s != nullptr) {
      stmt->stmts.push_back(s);
    }
  }
  Expect(TokenKind::kKwEnd);
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
  Consume();  // case/casex/casez
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
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

Stmt* Parser::ParseForStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFor;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFor);
  Expect(TokenKind::kLParen);
  stmt->for_init = ParseAssignmentOrExprStmt();
  stmt->for_cond = ParseExpr();
  Expect(TokenKind::kSemicolon);
  stmt->for_step = ParseAssignmentOrExprStmt();
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

Stmt* Parser::ParseForkStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFork;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFork);
  while (!Check(TokenKind::kKwJoin) && !Check(TokenKind::kKwJoinAny) &&
         !Check(TokenKind::kKwJoinNone) && !AtEnd()) {
    auto* s = ParseStmt();
    if (s != nullptr) {
      stmt->fork_stmts.push_back(s);
    }
  }
  stmt->join_kind = CurrentToken().kind;
  Consume();  // join / join_any / join_none
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
  stmt->kind = StmtKind::kWait;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWait);
  Expect(TokenKind::kLParen);
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen);
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseDisableStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDisable;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDisable);
  stmt->expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

Stmt* Parser::ParseAssignmentOrExprStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  // Parse prefix/primary first — stop before infix operators so that
  // '<=' is available for nonblocking assignment detection.
  auto* lhs_expr = ParsePrefixExpr();

  if (Match(TokenKind::kEq)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    stmt->rhs = ParseExpr();
  } else if (Match(TokenKind::kLtEq)) {
    stmt->kind = StmtKind::kNonblockingAssign;
    stmt->lhs = lhs_expr;
    stmt->rhs = ParseExpr();
  } else {
    // Not an assignment — complete the expression via infix parsing.
    stmt->kind = StmtKind::kExprStmt;
    stmt->expr = ParseInfixBp(lhs_expr, 0);
  }
  Expect(TokenKind::kSemicolon);
  return stmt;
}

// --- Types ---

static std::optional<DataTypeKind> TokenToTypeKind(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwLogic:
    case TokenKind::kKwWire:
      return DataTypeKind::kLogic;
    case TokenKind::kKwReg:
      return DataTypeKind::kReg;
    case TokenKind::kKwBit:
      return DataTypeKind::kBit;
    case TokenKind::kKwByte:
      return DataTypeKind::kByte;
    case TokenKind::kKwShortint:
      return DataTypeKind::kShortint;
    case TokenKind::kKwInt:
      return DataTypeKind::kInt;
    case TokenKind::kKwLongint:
      return DataTypeKind::kLongint;
    case TokenKind::kKwInteger:
      return DataTypeKind::kInteger;
    case TokenKind::kKwReal:
      return DataTypeKind::kReal;
    case TokenKind::kKwTime:
      return DataTypeKind::kTime;
    case TokenKind::kKwString:
      return DataTypeKind::kString;
    default:
      return std::nullopt;
  }
}

DataType Parser::ParseDataType() {
  DataType dtype;
  auto kind = TokenToTypeKind(CurrentToken().kind);
  if (!kind) return dtype;
  dtype.kind = *kind;
  Consume();

  if (Match(TokenKind::kKwSigned)) {
    dtype.is_signed = true;
  } else if (Match(TokenKind::kKwUnsigned)) {
    dtype.is_signed = false;
  }

  if (Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }
  return dtype;
}

// --- Event lists ---

std::vector<EventExpr> Parser::ParseEventList() {
  std::vector<EventExpr> events;
  events.push_back(ParseSingleEvent());
  while (Match(TokenKind::kKwOr) || Match(TokenKind::kComma)) {
    events.push_back(ParseSingleEvent());
  }
  return events;
}

EventExpr Parser::ParseSingleEvent() {
  EventExpr ev;
  if (Match(TokenKind::kKwPosedge)) {
    ev.edge = Edge::kPosedge;
  } else if (Match(TokenKind::kKwNegedge)) {
    ev.edge = Edge::kNegedge;
  }
  ev.signal = ParseExpr();
  return ev;
}

Stmt* Parser::ParseDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHash);
  stmt->delay = ParsePrimaryExpr();
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseEventControlStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kEventControl;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kAt);
  if (Match(TokenKind::kStar)) {
    // @* — implicit sensitivity
  } else {
    Expect(TokenKind::kLParen);
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen);
  }
  stmt->body = ParseStmt();
  return stmt;
}

}  // namespace delta
