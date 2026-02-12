#include "parser/parser.h"

#include <cctype>
#include <optional>

#include "common/types.h"

namespace delta {

Parser::Parser(Lexer& lexer, Arena& arena, DiagEngine& diag)
    : lexer_(lexer), arena_(arena), diag_(diag) {
  // §9.7: process is a built-in class type
  known_types_.insert("process");
  // §19.4: semaphore and mailbox are built-in class types
  known_types_.insert("semaphore");
  known_types_.insert("mailbox");
}

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

// §18.5.1: out-of-block constraint — constraint class_id::name { ... }
void Parser::ParseOutOfBlockConstraint(CompilationUnit* unit) {
  Consume();  // constraint
  ExpectIdentifier();
  Expect(TokenKind::kColonColon);
  ExpectIdentifier();
  Expect(TokenKind::kLBrace);
  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      Consume();
    }
  }
  (void)unit;
}

// Parse secondary top-level items (primitives, checkers, configs, etc.)
bool Parser::TryParseSecondaryTopLevel(CompilationUnit* unit) {
  if (Check(TokenKind::kKwPrimitive)) {
    unit->udps.push_back(ParseUdpDecl());
    return true;
  }
  if (Check(TokenKind::kKwChecker)) {
    unit->checkers.push_back(ParseCheckerDecl());
    return true;
  }
  if (Check(TokenKind::kKwConfig)) {
    unit->configs.push_back(ParseConfigDecl());
    return true;
  }
  if (Check(TokenKind::kKwFunction)) {
    unit->cu_items.push_back(ParseFunctionDecl());
    return true;
  }
  if (Check(TokenKind::kKwTask)) {
    unit->cu_items.push_back(ParseTaskDecl());
    return true;
  }
  if (Check(TokenKind::kKwConstraint)) {
    ParseOutOfBlockConstraint(unit);
    return true;
  }
  return false;
}

void Parser::ParseTopLevel(CompilationUnit* unit) {
  if (Match(TokenKind::kSemicolon)) return;  // null item
  ParseAttributes();                         // consume optional (* ... *)
  if (Check(TokenKind::kKwExtern)) {
    ParseExternTopLevel(unit);
    return;
  }
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseModuleDecl());
    return;
  }
  if (Check(TokenKind::kKwPackage)) {
    unit->packages.push_back(ParsePackageDecl());
    return;
  }
  if (IsAtClassDecl()) {
    unit->classes.push_back(ParseClassDecl());
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
  if (Check(TokenKind::kKwTypedef)) {
    std::vector<ModuleItem*> discard;
    ParseModuleItem(discard);
    return;
  }
  if (TryParseSecondaryTopLevel(unit)) return;
  diag_.Error(CurrentLoc(), "expected top-level declaration");
  Consume();
}

void Parser::ParseExternTopLevel(CompilationUnit* unit) {
  Consume();  // extern
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseExternModuleDecl());
    return;
  }
  SkipToSemicolon(lexer_);
}

// --- Module parsing ---

ModuleDecl* Parser::ParseExternModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  mod->is_extern = true;
  mod->range.start = CurrentLoc();
  if (!Match(TokenKind::kKwMacromodule)) {
    Expect(TokenKind::kKwModule);
  }
  mod->name = Expect(TokenKind::kIdentifier).text;
  ParseParamsPortsAndSemicolon(*mod);
  mod->range.end = CurrentLoc();
  return mod;
}

ModuleDecl* Parser::ParseModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  auto loc = CurrentLoc();
  if (!Match(TokenKind::kKwMacromodule)) {
    Expect(TokenKind::kKwModule);
  }

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
  // DPI-C import: import "DPI-C" ...
  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiImport());
    return;
  }
  items.push_back(ParseImportItem());
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseImportItem());
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseExportDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwExport);
  // DPI-C export: export "DPI-C" ...
  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiExport(loc));
    return;
  }
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

ModuleItem* Parser::ParseDpiImport() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiImport;
  item->loc = CurrentLoc();
  Consume();  // string literal "DPI-C"

  // Optional: pure or context
  if (Match(TokenKind::kKwPure)) {
    item->dpi_is_pure = true;
  }
  if (Match(TokenKind::kKwContext)) {
    item->dpi_is_context = true;
  }

  // Optional: c_identifier = (lookahead for identifier followed by '=')
  if (Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Match(TokenKind::kEq)) {
      item->dpi_c_name = tok.text;
    } else {
      lexer_.RestorePos(saved);
    }
  }

  // function or task
  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }

  // Parse return type (for functions) and name
  if (!item->dpi_is_task) {
    item->return_type = ParseDataType();
  }
  item->name = Expect(TokenKind::kIdentifier).text;

  // Optional argument list
  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseDpiExport(SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiExport;
  item->loc = loc;
  Consume();  // string literal "DPI-C"

  // Optional: c_identifier =
  if (Check(TokenKind::kIdentifier)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Match(TokenKind::kEq)) {
      item->dpi_c_name = tok.text;
    } else {
      lexer_.RestorePos(saved);
    }
  }

  // function or task
  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }
  item->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);
  return item;
}

void Parser::ParseParamPortDecl(
    std::vector<std::pair<std::string_view, Expr*>>& params) {
  Match(TokenKind::kKwParameter);
  // Handle type parameter: #(type T = real)  (§6.20.3)
  if (Match(TokenKind::kKwType)) {
    auto name = Expect(TokenKind::kIdentifier);
    if (Match(TokenKind::kEq)) {
      if (Check(TokenKind::kKwType)) {
        ParseExpr();  // type() expression as default
      } else {
        ParseDataType();  // consume default type
      }
    }
    params.push_back({name.text, nullptr});
    known_types_.insert(name.text);
    return;
  }
  ParseDataType();  // consume optional type (not stored in params)
  auto name = Expect(TokenKind::kIdentifier);
  Expr* default_val = nullptr;
  if (Match(TokenKind::kEq)) {
    default_val = ParseExpr();
  }
  params.push_back({name.text, default_val});
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
      ParseParamPortDecl(decl.params);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl.params);
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
  if (CheckIdentifier()) {
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
    port.name = ExpectIdentifier().text;
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

  // Handle implicit type with packed dims: input [3:0] a (§6.10)
  if (port.data_type.kind == DataTypeKind::kImplicit &&
      Check(TokenKind::kLBracket)) {
    port.data_type.kind = DataTypeKind::kLogic;
    Consume();
    port.data_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    port.data_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  auto name_tok = ExpectIdentifier();
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
  auto* prev_module = current_module_;
  current_module_ = &mod;
  bool non_ansi = HasNonAnsiPorts(mod);
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;  // null module item
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(mod);
      continue;
    }
    ParseModuleItem(mod.items);
  }
  current_module_ = prev_module;
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

// §11.12: let declaration — let name(args) = expr;
ModuleItem* Parser::ParseLetDecl() {
  Consume();  // 'let'
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = CurrentLoc();
  item->name = ExpectIdentifier().text;
  if (Check(TokenKind::kLParen)) {
    std::vector<Expr*> discard;
    ParseParenList(discard);
  }
  Expect(TokenKind::kEq);
  item->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return item;
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

static bool TryParseTimeUnit(std::string_view text, TimeUnit& out) {
  // Extract the unit suffix from a time literal like "1ns", "100us".
  size_t i = 0;
  while (
      i < text.size() &&
      (std::isdigit(static_cast<unsigned char>(text[i])) || text[i] == '.')) {
    ++i;
  }
  auto suffix = text.substr(i);
  return ParseTimeUnitStr(suffix, out);
}

void Parser::ParseTimeunitDecl(ModuleDecl* mod) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  Consume();             // timeunit or timeprecision keyword
  auto tok = Consume();  // time literal (e.g. 1ns)
  if (mod != nullptr) {
    TimeUnit unit = TimeUnit::kNs;
    TryParseTimeUnit(tok.text, unit);
    if (is_unit) {
      mod->time_unit = unit;
      mod->has_timeunit = true;
    } else {
      mod->time_prec = unit;
      mod->has_timeprecision = true;
    }
  }
  if (Match(TokenKind::kSlash)) {
    auto prec_tok = Consume();  // second time literal
    if (mod != nullptr && is_unit) {
      TimeUnit prec = TimeUnit::kNs;
      TryParseTimeUnit(prec_tok.text, prec);
      mod->time_prec = prec;
      mod->has_timeprecision = true;
    }
  }
  Expect(TokenKind::kSemicolon);
}

bool Parser::TryParseClockingOrVerification(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwSpecify)) {
    items.push_back(ParseSpecifyBlock());
    return true;
  }
  if (Check(TokenKind::kKwSpecparam)) {
    items.push_back(ParseSpecparamDecl());
    return true;
  }
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

bool Parser::TryParseProcessBlock(std::vector<ModuleItem*>& items) {
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

bool Parser::IsAtClassDecl() {
  if (Check(TokenKind::kKwClass)) return true;
  // 'virtual class' or 'interface class' — need lookahead to distinguish
  // from 'virtual interface' or plain 'interface'.
  if (!Check(TokenKind::kKwVirtual) && !Check(TokenKind::kKwInterface)) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();  // consume 'virtual' or 'interface'
  bool result = Check(TokenKind::kKwClass);
  lexer_.RestorePos(saved);
  return result;
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
  if (TryParseProcessBlock(items)) return true;
  if (Check(TokenKind::kKwAlias)) {
    items.push_back(ParseAlias());
    return true;
  }
  if (Check(TokenKind::kKwGenvar)) {
    ParseGenvarDecl(items);
    return true;
  }
  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParseTimeunitDecl(current_module_);
    return true;
  }
  if (Check(TokenKind::kKwLet)) {
    items.push_back(ParseLetDecl());
    return true;
  }
  if (Check(TokenKind::kKwInterconnect)) {
    Consume();
    DataType dtype;
    dtype.kind = DataTypeKind::kWire;
    dtype.is_net = true;
    dtype.is_interconnect = true;
    ParseVarDeclList(items, dtype);
    return true;
  }
  return TryParseClassOrVerification(items);
}

bool Parser::TryParseClassOrVerification(std::vector<ModuleItem*>& items) {
  if (IsAtClassDecl()) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kClassDecl;
    item->loc = CurrentLoc();
    item->class_decl = ParseClassDecl();
    if (item->class_decl) item->name = item->class_decl->name;
    items.push_back(item);
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
  // Handle 'var' prefix: var type(expr) name; or var data_type name; (§6.8)
  if (Match(TokenKind::kKwVar)) {
    if (Check(TokenKind::kKwType)) {
      Consume();  // type
      Expect(TokenKind::kLParen);
      auto* type_expr = ParseExpr();
      Expect(TokenKind::kRParen);
      auto* item = arena_.Create<ModuleItem>();
      item->kind = ModuleItemKind::kVarDecl;
      item->loc = CurrentLoc();
      // §6.23: Store the type reference for elaboration.
      item->data_type.type_ref_expr = type_expr;
      item->name = ExpectIdentifier().text;
      ParseUnpackedDims(item->unpacked_dims);
      Expect(TokenKind::kSemicolon);
      items.push_back(item);
      return;
    }
    auto dtype = ParseDataType();
    ParseVarDeclList(items, dtype);
    return;
  }
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
  if (!CheckIdentifier()) {
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
    auto type_tok = ExpectIdentifier();
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
  if (CheckIdentifier() || Check(TokenKind::kHash)) {
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

}  // namespace delta
