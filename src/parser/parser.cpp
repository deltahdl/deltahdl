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

static void SkipToSemicolon(Lexer& lexer) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

CompilationUnit* Parser::Parse() {
  auto* unit = arena_.Create<CompilationUnit>();
  while (!AtEnd()) {
    ParseTopLevel(unit);
  }
  return unit;
}

void Parser::ParseTopLevel(CompilationUnit* unit) {
  if (Check(TokenKind::kKwExtern)) {
    Consume();
    if (Check(TokenKind::kKwModule)) {
      unit->modules.push_back(ParseExternModuleDecl());
    } else {
      SkipToSemicolon(lexer_);
    }
    return;
  }
  if (Check(TokenKind::kKwModule)) {
    unit->modules.push_back(ParseModuleDecl());
    return;
  }
  if (Check(TokenKind::kKwPackage)) {
    unit->packages.push_back(ParsePackageDecl());
    return;
  }
  if (Check(TokenKind::kKwInterface)) {
    unit->interfaces.push_back(ParseInterfaceDecl());
    return;
  }
  if (Check(TokenKind::kKwProgram)) {
    unit->programs.push_back(ParseProgramDecl());
    return;
  }
  if (Check(TokenKind::kKwClass) || Check(TokenKind::kKwVirtual)) {
    unit->classes.push_back(ParseClassDecl());
    return;
  }
  if (Check(TokenKind::kKwPrimitive)) {
    unit->udps.push_back(ParseUdpDecl());
    return;
  }
  if (Check(TokenKind::kKwChecker)) {
    unit->checkers.push_back(ParseCheckerDecl());
    return;
  }
  diag_.Error(CurrentLoc(), "expected top-level declaration");
  Consume();
}

// --- Module parsing ---

ModuleDecl* Parser::ParseExternModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  mod->is_extern = true;
  mod->range.start = CurrentLoc();
  Expect(TokenKind::kKwModule);
  mod->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*mod);
  mod->range.end = CurrentLoc();
  return mod;
}

ModuleDecl* Parser::ParseModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwModule);

  // Optional lifetime qualifier (§3.4)
  Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);

  auto name_tok = Expect(TokenKind::kIdentifier);
  mod->name = name_tok.text;
  mod->range.start = loc;

  ParseParamsPortsAndSemicolon(*mod);
  ParseModuleBody(*mod);
  Expect(TokenKind::kKwEndmodule);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
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
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  pkg->range.end = CurrentLoc();
  return pkg;
}

ModuleItem* Parser::ParseImportItem() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kImportDecl;
  item->loc = CurrentLoc();
  item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kColonColon);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
  }
  return item;
}

void Parser::ParseImportDecl(std::vector<ModuleItem*>& items) {
  Expect(TokenKind::kKwImport);
  items.push_back(ParseImportItem());
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseImportItem());
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseExportDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwExport);
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
    // export *::*;
    item->import_item.package_name = "*";
    Expect(TokenKind::kColonColon);
    Expect(TokenKind::kStar);
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kColonColon);
    if (Match(TokenKind::kStar)) {
      item->import_item.is_wildcard = true;
    } else {
      item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
    }
  }
  items.push_back(item);
  Expect(TokenKind::kSemicolon);
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
  // Optional package imports in module header (§26.4)
  while (Check(TokenKind::kKwImport)) {
    ParseImportDecl(decl.items);
  }
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

static bool IsPortDirection(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef;
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }
  // Detect non-ANSI style: first token is an identifier (no direction).
  if (Check(TokenKind::kIdentifier)) {
    ParseNonAnsiPortList(mod);
    return;
  }
  mod.ports.push_back(ParsePortDecl());
  while (Match(TokenKind::kComma)) {
    mod.ports.push_back(ParsePortDecl());
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseNonAnsiPortList(ModuleDecl& mod) {
  // Non-ANSI: module m(a, b, c); -- just identifier names.
  do {
    PortDecl port;
    port.loc = CurrentLoc();
    port.name = Expect(TokenKind::kIdentifier).text;
    mod.ports.push_back(port);
  } while (Match(TokenKind::kComma));
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

static bool HasNonAnsiPorts(const ModuleDecl& mod) {
  if (mod.ports.empty()) return false;
  return mod.ports[0].direction == Direction::kNone;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  bool non_ansi = HasNonAnsiPorts(mod);
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(mod);
      continue;
    }
    ParseModuleItem(mod.items);
  }
}

void Parser::ParseNonAnsiPortDecls(ModuleDecl& mod) {
  Direction dir = Direction::kNone;
  auto tk = CurrentToken().kind;
  if (tk == TokenKind::kKwInput) dir = Direction::kInput;
  if (tk == TokenKind::kKwOutput) dir = Direction::kOutput;
  if (tk == TokenKind::kKwInout) dir = Direction::kInout;
  if (tk == TokenKind::kKwRef) dir = Direction::kRef;
  Consume();  // direction keyword

  auto dtype = ParseDataType();

  // Handle implicit type with packed dims: input [7:0] a;
  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  // Parse comma-separated names: input [7:0] a, b;
  do {
    auto name = Expect(TokenKind::kIdentifier).text;
    for (auto& port : mod.ports) {
      if (port.name != name) continue;
      port.direction = dir;
      port.data_type = dtype;
      break;
    }
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
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

void Parser::ParseGenvarDecl(std::vector<ModuleItem*>& items) {
  Consume();  // genvar keyword
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->name = Expect(TokenKind::kIdentifier).text;
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseTimeunitDecl() {
  Consume();  // timeunit or timeprecision keyword
  Consume();  // time literal (e.g. 1ns)
  if (Match(TokenKind::kSlash)) {
    Consume();  // second time literal
  }
  Expect(TokenKind::kSemicolon);
}

bool Parser::TryParseClockingOrVerification(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwClocking)) {
    items.push_back(ParseClockingDecl());
    return true;
  }
  if (Check(TokenKind::kKwDefault) || Check(TokenKind::kKwGlobal)) {
    auto saved = lexer_.SavePos();
    Consume();
    bool is_clocking = Check(TokenKind::kKwClocking);
    lexer_.RestorePos(saved);
    if (is_clocking) {
      items.push_back(ParseClockingDecl());
      return true;
    }
  }
  return TryParseVerificationItem(items);
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
  if (Check(TokenKind::kKwAlias)) {
    items.push_back(ParseAlias());
    return true;
  }
  if (Check(TokenKind::kKwGenvar)) {
    ParseGenvarDecl(items);
    return true;
  }
  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParseTimeunitDecl();
    return true;
  }
  return TryParseClockingOrVerification(items);
}

bool Parser::TryParseVerificationItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwAssert)) {
    items.push_back(ParseAssertProperty());
    return true;
  }
  if (Check(TokenKind::kKwAssume)) {
    items.push_back(ParseAssumeProperty());
    return true;
  }
  if (Check(TokenKind::kKwCover)) {
    items.push_back(ParseCoverProperty());
    return true;
  }
  if (Check(TokenKind::kKwProperty)) {
    items.push_back(ParsePropertyDecl());
    return true;
  }
  if (Check(TokenKind::kKwSequence)) {
    items.push_back(ParseSequenceDecl());
    return true;
  }
  if (Check(TokenKind::kKwCovergroup)) {
    ParseCovergroupDecl(items);
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
    ParseImportDecl(items);
    AttachAttrs(items, before, attrs);
    return;
  }
  if (Check(TokenKind::kKwExport)) {
    ParseExportDecl(items);
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
    ParseGateInst(items);
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
  // Instance array range: inst_name [left:right] or [size] (§23.3.2)
  if (Check(TokenKind::kLBracket)) {
    Consume();
    item->inst_range_left = ParseExpr();
    if (Match(TokenKind::kColon)) {
      item->inst_range_right = ParseExpr();
    }
    Expect(TokenKind::kRBracket);
  }
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
  if (Check(TokenKind::kDotStar)) {
    // .* wildcard port connection (§23.3.2.4)
    Consume();
    item->inst_wildcard = true;
    return;
  }
  if (Match(TokenKind::kDot)) {
    auto name = Expect(TokenKind::kIdentifier);
    Expect(TokenKind::kLParen);
    Expr* expr = nullptr;
    if (!Check(TokenKind::kRParen)) {
      expr = ParseExpr();
    }
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
  // Optional delay: assign #(delay) or assign #delay
  if (Check(TokenKind::kHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      ParseMinTypMaxExpr();  // consume but don't store (TODO: store delay)
      Expect(TokenKind::kRParen);
    } else {
      ParsePrimaryExpr();  // consume simple delay
    }
  }
  item->assign_lhs = ParseExpr();
  Expect(TokenKind::kEq);
  item->assign_rhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseAlias() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAlias;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwAlias);
  item->alias_nets.push_back(ParseExpr());
  while (Match(TokenKind::kEq)) {
    item->alias_nets.push_back(ParseExpr());
  }
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
    if (Match(TokenKind::kStar)) {
      // @* — implicit sensitivity (§9.4.2.2)
    } else if (Check(TokenKind::kLParen)) {
      Consume();
      if (Match(TokenKind::kStar)) {
        // @(*) — implicit sensitivity (§9.4.2.2)
      } else {
        item->sensitivity = ParseEventList();
      }
      Expect(TokenKind::kRParen);
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
    case TokenKind::kKwWire:
      return DataTypeKind::kWire;
    case TokenKind::kKwTri:
      return DataTypeKind::kTri;
    case TokenKind::kKwTriand:
      return DataTypeKind::kTriand;
    case TokenKind::kKwTrior:
      return DataTypeKind::kTrior;
    case TokenKind::kKwTri0:
      return DataTypeKind::kTri0;
    case TokenKind::kKwTri1:
      return DataTypeKind::kTri1;
    case TokenKind::kKwTrireg:
      return DataTypeKind::kTrireg;
    case TokenKind::kKwWand:
      return DataTypeKind::kWand;
    case TokenKind::kKwWor:
      return DataTypeKind::kWor;
    case TokenKind::kKwSupply0:
      return DataTypeKind::kSupply0;
    case TokenKind::kKwSupply1:
      return DataTypeKind::kSupply1;
    case TokenKind::kKwUwire:
      return DataTypeKind::kUwire;
    default:
      return std::nullopt;
  }
}

DataType Parser::ParseDataType() {
  DataType dtype;

  if (Match(TokenKind::kKwConst)) {
    dtype.is_const = true;
  }

  // Virtual interface type: virtual [interface] type_name [.modport] (§25.9)
  if (Check(TokenKind::kKwVirtual)) {
    Consume();
    dtype.kind = DataTypeKind::kVirtualInterface;
    Match(TokenKind::kKwInterface);  // optional 'interface' keyword
    dtype.type_name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kDot)) {
      dtype.modport_name = Expect(TokenKind::kIdentifier).text;
    }
    return dtype;
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

  // vectored/scalared qualifiers (§6.6.9) — net types only
  if (dtype.is_net) {
    if (Match(TokenKind::kKwVectored)) {
      dtype.is_vectored = true;
    } else if (Match(TokenKind::kKwScalared)) {
      dtype.is_scalared = true;
    }
  }

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

Token Parser::ExpectIdentifier() {
  if (CheckIdentifier()) {
    return Consume();
  }
  auto tok = CurrentToken();
  diag_.Error(tok.loc, "expected identifier, got " +
                           std::string(TokenKindName(tok.kind)));
  return tok;
}

bool Parser::CheckIdentifier() { return Check(TokenKind::kIdentifier); }

}  // namespace delta
