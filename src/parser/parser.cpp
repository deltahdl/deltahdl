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
    // Parameter port list: #(param_decls)
    Consume();
    Expect(TokenKind::kLParen);
    // Simplified: skip parameter parsing for now
    while (!Check(TokenKind::kRParen) && !AtEnd()) {
      Consume();
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
    auto* item = ParseModuleItem();
    if (item != nullptr) {
      mod.items.push_back(item);
    }
  }
}

ModuleItem* Parser::ParseModuleItem() {
  if (Check(TokenKind::kKwAssign)) {
    return ParseContinuousAssign();
  }
  if (Check(TokenKind::kKwInitial)) {
    return ParseInitialBlock();
  }
  if (Check(TokenKind::kKwFinal)) {
    return ParseFinalBlock();
  }
  if (Check(TokenKind::kKwAlways)) {
    return ParseAlwaysBlock(AlwaysKind::kAlways);
  }
  if (Check(TokenKind::kKwAlwaysComb)) {
    return ParseAlwaysBlock(AlwaysKind::kAlwaysComb);
  }
  if (Check(TokenKind::kKwAlwaysFF)) {
    return ParseAlwaysBlock(AlwaysKind::kAlwaysFF);
  }
  if (Check(TokenKind::kKwAlwaysLatch)) {
    return ParseAlwaysBlock(AlwaysKind::kAlwaysLatch);
  }
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    return ParseParamDecl();
  }
  // Try net/var declaration
  auto dtype = ParseDataType();
  if (dtype.kind != DataTypeKind::kImplicit || Check(TokenKind::kIdentifier)) {
    return ParseNetOrVarDecl(dtype);
  }
  diag_.Error(CurrentLoc(), "unexpected token in module body");
  Synchronize();
  return nullptr;
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

ModuleItem* Parser::ParseNetOrVarDecl(const DataType& dtype) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = CurrentLoc();
  item->data_type = dtype;
  auto name_tok = Expect(TokenKind::kIdentifier);
  item->name = name_tok.text;
  if (Match(TokenKind::kEq)) {
    item->init_expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Statements ---

Stmt* Parser::ParseStmt() {
  if (Check(TokenKind::kKwBegin)) {
    return ParseBlockStmt();
  }
  if (Check(TokenKind::kKwIf)) {
    return ParseIfStmt();
  }
  if (Check(TokenKind::kKwCase) || Check(TokenKind::kKwCasex) ||
      Check(TokenKind::kKwCasez)) {
    auto kind = CurrentToken().kind;
    return ParseCaseStmt(kind);
  }
  if (Check(TokenKind::kKwFor)) {
    return ParseForStmt();
  }
  if (Check(TokenKind::kKwWhile)) {
    return ParseWhileStmt();
  }
  if (Check(TokenKind::kKwForever)) {
    return ParseForeverStmt();
  }
  if (Check(TokenKind::kKwRepeat)) {
    return ParseRepeatStmt();
  }
  if (Check(TokenKind::kKwFork)) {
    return ParseForkStmt();
  }
  if (Check(TokenKind::kHash)) {
    return ParseDelayStmt();
  }
  if (Check(TokenKind::kAt)) {
    return ParseEventControlStmt();
  }
  return ParseAssignmentOrExprStmt();
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

Stmt* Parser::ParseAssignmentOrExprStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  auto* lhs_expr = ParseExpr();

  if (Match(TokenKind::kEq)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    stmt->rhs = ParseExpr();
  } else if (Match(TokenKind::kLtEq)) {
    stmt->kind = StmtKind::kNonblockingAssign;
    stmt->lhs = lhs_expr;
    stmt->rhs = ParseExpr();
  } else {
    stmt->kind = StmtKind::kExprStmt;
    stmt->expr = lhs_expr;
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
