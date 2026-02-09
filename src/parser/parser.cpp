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
    if (Check(TokenKind::kKwEndmodule) || Check(TokenKind::kKwEndpackage) ||
        Check(TokenKind::kKwEndinterface) || Check(TokenKind::kKwEndprogram) ||
        Check(TokenKind::kKwEndclass) || Check(TokenKind::kKwEnd)) {
      return;
    }
    Consume();
  }
}

// --- Attributes (§5.12) ---

std::vector<Attribute> Parser::ParseAttributes() {
  std::vector<Attribute> attrs;
  while (Check(TokenKind::kAttrStart)) {
    Consume();  // skip (*
    do {
      Attribute attr;
      attr.name = Expect(TokenKind::kIdentifier).text;
      if (Match(TokenKind::kEq)) {
        attr.value = ParseExpr();
      }
      attrs.push_back(attr);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kAttrEnd);
  }
  return attrs;
}

void Parser::AttachAttrs(std::vector<ModuleItem*>& items, size_t before,
                         const std::vector<Attribute>& attrs) {
  if (attrs.empty()) return;
  for (size_t i = before; i < items.size(); ++i) {
    items[i]->attrs = attrs;
  }
}

// --- Top level ---

CompilationUnit* Parser::Parse() {
  auto* unit = arena_.Create<CompilationUnit>();
  while (!AtEnd()) {
    if (Check(TokenKind::kKwModule)) {
      unit->modules.push_back(ParseModuleDecl());
      continue;
    }
    if (Check(TokenKind::kKwPackage)) {
      unit->packages.push_back(ParsePackageDecl());
      continue;
    }
    if (Check(TokenKind::kKwInterface)) {
      unit->interfaces.push_back(ParseInterfaceDecl());
      continue;
    }
    if (Check(TokenKind::kKwProgram)) {
      unit->programs.push_back(ParseProgramDecl());
      continue;
    }
    if (Check(TokenKind::kKwClass) || Check(TokenKind::kKwVirtual)) {
      unit->classes.push_back(ParseClassDecl());
      continue;
    }
    diag_.Error(CurrentLoc(), "expected top-level declaration");
    Consume();
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

  ParseParamsPortsAndSemicolon(*mod);
  ParseModuleBody(*mod);
  Expect(TokenKind::kKwEndmodule);
  mod->range.end = CurrentLoc();
  return mod;
}

PackageDecl* Parser::ParsePackageDecl() {
  auto* pkg = arena_.Create<PackageDecl>();
  pkg->range.start = CurrentLoc();
  Expect(TokenKind::kKwPackage);
  pkg->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);
  while (!Check(TokenKind::kKwEndpackage) && !AtEnd()) {
    ParseModuleItem(pkg->items);
  }
  Expect(TokenKind::kKwEndpackage);
  pkg->range.end = CurrentLoc();
  return pkg;
}

ModuleItem* Parser::ParseImportDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kImportDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwImport);
  item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kColonColon);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
  }
  Expect(TokenKind::kSemicolon);
  return item;
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

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      ParseParamPortDecl(decl);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl);
      }
    }
    Expect(TokenKind::kRParen);
  }
  if (Check(TokenKind::kLParen)) {
    ParsePortList(decl);
  }
  Expect(TokenKind::kSemicolon);
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

bool Parser::TryParseKeywordItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwTypedef)) {
    items.push_back(ParseTypedef());
    return true;
  }
  if (Check(TokenKind::kKwNettype)) {
    items.push_back(ParseNettypeDecl());
    return true;
  }
  if (Check(TokenKind::kKwFunction)) {
    items.push_back(ParseFunctionDecl());
    return true;
  }
  if (Check(TokenKind::kKwTask)) {
    items.push_back(ParseTaskDecl());
    return true;
  }
  if (Check(TokenKind::kKwAssign)) {
    items.push_back(ParseContinuousAssign());
    return true;
  }
  if (Check(TokenKind::kKwInitial)) {
    items.push_back(ParseInitialBlock());
    return true;
  }
  if (Check(TokenKind::kKwFinal)) {
    items.push_back(ParseFinalBlock());
    return true;
  }
  auto ak = TokenToAlwaysKind(CurrentToken().kind);
  if (ak) {
    items.push_back(ParseAlwaysBlock(*ak));
    return true;
  }
  return false;
}

void Parser::ParseModuleItem(std::vector<ModuleItem*>& items) {
  auto attrs = ParseAttributes();
  size_t before = items.size();

  if (TryParseKeywordItem(items)) {
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    items.push_back(ParseParamDecl());
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwDefparam)) {
    items.push_back(ParseDefparam());
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwImport)) {
    items.push_back(ParseImportDecl());
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwGenerate)) {
    ParseGenerateRegion(items);
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwFor)) {
    items.push_back(ParseGenerateFor());
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwIf)) {
    items.push_back(ParseGenerateIf());
    AttachAttrs(items, before, attrs);
    return;
  }
  ParseTypedItemOrInst(items);
  AttachAttrs(items, before, attrs);
}

void Parser::ParseTypedItemOrInst(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwCase)) {
    items.push_back(ParseGenerateCase());
    return;
  }
  if (IsAtGateKeyword()) {
    items.push_back(ParseGateInst());
    return;
  }
  if (Check(TokenKind::kKwEnum)) {
    auto dtype = ParseEnumType();
    ParseVarDeclList(items, dtype);
    return;
  }
  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    auto dtype = ParseStructOrUnionType();
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
  if (Check(TokenKind::kColonColon)) {
    Consume();  // '::'
    auto type_tok = Expect(TokenKind::kIdentifier);
    DataType dtype;
    dtype.kind = DataTypeKind::kNamed;
    dtype.scope_name = name_tok.text;
    dtype.type_name = type_tok.text;
    ParseVarDeclList(items, dtype);
    return;
  }
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

void Parser::ParseUnpackedDims(std::vector<Expr*>& dims) {
  while (Check(TokenKind::kLBracket)) {
    Consume();
    if (Match(TokenKind::kRBracket)) {
      dims.push_back(nullptr);  // dynamic array []
      continue;
    }
    if (Match(TokenKind::kDollar)) {
      // Queue: [$] or [$:N]
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = "$";
      if (Match(TokenKind::kColon)) {
        dim->rhs = ParseExpr();
      }
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }
    if (Match(TokenKind::kStar)) {
      // Associative: [*]
      auto* dim = arena_.Create<Expr>();
      dim->kind = ExprKind::kIdentifier;
      dim->text = "*";
      dims.push_back(dim);
      Expect(TokenKind::kRBracket);
      continue;
    }
    auto* expr = ParseExpr();
    dims.push_back(expr);
    Expect(TokenKind::kRBracket);
  }
}

void Parser::ParseVarDeclList(std::vector<ModuleItem*>& items,
                              const DataType& dtype) {
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind =
        dtype.is_net ? ModuleItemKind::kNetDecl : ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->data_type = dtype;
    item->name = Expect(TokenKind::kIdentifier).text;
    ParseUnpackedDims(item->unpacked_dims);
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
  // Handle "parameter type T = ..." (type parameter).
  if (Match(TokenKind::kKwType)) {
    item->data_type.kind = DataTypeKind::kVoid;  // Marker for type params.
  } else {
    item->data_type = ParseDataType();
  }
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
    case TokenKind::kArrow: {
      auto* s = arena_.Create<Stmt>();
      s->kind = StmtKind::kEventTrigger;
      s->range.start = CurrentLoc();
      Consume();
      s->expr = ParseExpr();
      Expect(TokenKind::kSemicolon);
      return s;
    }
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

Stmt* Parser::ParseAssignmentOrExprNoSemi() {
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
  return stmt;
}

Stmt* Parser::ParseAssignmentOrExprStmt() {
  auto* stmt = ParseAssignmentOrExprNoSemi();
  Expect(TokenKind::kSemicolon);
  return stmt;
}

// --- Types ---

static bool IsNetTypeToken(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwWire:
    case TokenKind::kKwTri:
    case TokenKind::kKwTriand:
    case TokenKind::kKwTrior:
    case TokenKind::kKwTri0:
    case TokenKind::kKwTri1:
    case TokenKind::kKwTrireg:
    case TokenKind::kKwWand:
    case TokenKind::kKwWor:
    case TokenKind::kKwSupply0:
    case TokenKind::kKwSupply1:
    case TokenKind::kKwUwire:
      return true;
    default:
      return false;
  }
}

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
    case TokenKind::kKwShortreal:
      return DataTypeKind::kShortreal;
    case TokenKind::kKwRealtime:
      return DataTypeKind::kRealtime;
    case TokenKind::kKwTime:
      return DataTypeKind::kTime;
    case TokenKind::kKwString:
      return DataTypeKind::kString;
    case TokenKind::kKwEvent:
      return DataTypeKind::kEvent;
    case TokenKind::kKwVoid:
      return DataTypeKind::kVoid;
    case TokenKind::kKwChandle:
      return DataTypeKind::kChandle;
    case TokenKind::kKwTri:
    case TokenKind::kKwTriand:
    case TokenKind::kKwTrior:
    case TokenKind::kKwTri0:
    case TokenKind::kKwTri1:
    case TokenKind::kKwTrireg:
    case TokenKind::kKwWand:
    case TokenKind::kKwWor:
    case TokenKind::kKwSupply0:
    case TokenKind::kKwSupply1:
    case TokenKind::kKwUwire:
      return DataTypeKind::kLogic;
    default:
      return std::nullopt;
  }
}

DataType Parser::ParseDataType() {
  DataType dtype;

  if (Match(TokenKind::kKwConst)) {
    dtype.is_const = true;
  }

  if (CurrentToken().Is(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) != 0) {
    dtype.kind = DataTypeKind::kNamed;
    dtype.type_name = Consume().text;
    return dtype;
  }

  auto tok_kind = CurrentToken().kind;
  auto kind = TokenToTypeKind(tok_kind);
  if (!kind) return dtype;
  dtype.kind = *kind;
  dtype.is_net = IsNetTypeToken(tok_kind);
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
  } else if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen);
  } else {
    // @ev — named event or bare signal shorthand.
    EventExpr ev;
    ev.signal = ParseExpr();
    stmt->events.push_back(ev);
  }
  stmt->body = ParseStmt();
  return stmt;
}

}  // namespace delta
