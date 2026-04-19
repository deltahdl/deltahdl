#include "parser/parser.h"

#include "common/types.h"
#include "parser/time_resolve.h"

namespace delta {

Parser::Parser(Lexer& lexer, Arena& arena, DiagEngine& diag)
    : lexer_(lexer), arena_(arena), diag_(diag) {
  // §9.7: process is a built-in class type
  known_types_.insert("process");
  // §19.4: semaphore and mailbox are built-in class types
  known_types_.insert("semaphore");
  known_types_.insert("mailbox");
  // §8.30: weak_reference is a built-in parameterized class
  known_types_.insert("weak_reference");
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

std::string_view Parser::ParseDottedPath() {
  auto first = ExpectIdentifier().text;
  std::string path(first);
  while (Match(TokenKind::kDot)) {
    path.push_back('.');
    auto next = ExpectIdentifier().text;
    path.append(next.data(), next.size());
  }
  auto* buf = static_cast<char*>(arena_.Allocate(path.size(), 1));
  std::copy_n(path.data(), path.size(), buf);
  return {buf, path.size()};
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
        Check(TokenKind::kKwEndchecker) || Check(TokenKind::kKwEndclass) ||
        Check(TokenKind::kKwEnd)) {
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
      auto tok = Expect(TokenKind::kIdentifier);
      attr.name = tok.text;
      attr.loc = tok.loc;
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

// --- Library source text (A.1.1) ---

CompilationUnit* Parser::ParseLibraryText() {
  auto* unit = arena_.Create<CompilationUnit>();
  while (!AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (Check(TokenKind::kKwLibrary)) {
      unit->libraries.push_back(ParseLibraryDecl());
    } else if (Check(TokenKind::kKwInclude)) {
      unit->lib_includes.push_back(ParseLibraryIncludeStmt());
    } else if (Check(TokenKind::kKwConfig)) {
      unit->configs.push_back(ParseConfigDecl());
    } else {
      diag_.Error(CurrentLoc(),
                  "expected library declaration, include statement, "
                  "config declaration, or ';'");
      Consume();
    }
  }
  return unit;
}

std::string_view Parser::ParseFilePathSpec() {
  auto tok = lexer_.NextFilePathSpec();
  if (tok.kind == TokenKind::kEof) {
    diag_.Error(CurrentLoc(), "expected file path specification");
    return {};
  }
  auto* buf = static_cast<char*>(arena_.Allocate(tok.text.size(), 1));
  std::copy_n(tok.text.data(), tok.text.size(), buf);
  return {buf, tok.text.size()};
}

LibraryDecl* Parser::ParseLibraryDecl() {
  auto* decl = arena_.Create<LibraryDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwLibrary);
  decl->name = Expect(TokenKind::kIdentifier).text;

  // Parse first file_path_spec (required).
  auto path = ParseFilePathSpec();
  if (path.empty()) {
    diag_.Error(CurrentLoc(), "expected at least one file path in library");
    Synchronize();
    return decl;
  }
  decl->file_paths.push_back(path);

  // Parse additional comma-separated file_path_specs.
  while (Match(TokenKind::kComma)) {
    decl->file_paths.push_back(ParseFilePathSpec());
  }

  // Parse optional -incdir clause.
  if (Check(TokenKind::kMinus)) {
    auto saved = lexer_.SavePos();
    Consume();  // '-'
    if (Check(TokenKind::kKwIncdir)) {
      Consume();  // 'incdir'
      decl->incdir_paths.push_back(ParseFilePathSpec());
      while (Match(TokenKind::kComma)) {
        decl->incdir_paths.push_back(ParseFilePathSpec());
      }
    } else {
      lexer_.RestorePos(saved);
    }
  }

  Expect(TokenKind::kSemicolon);
  decl->range.end = CurrentLoc();
  return decl;
}

IncludeStmt* Parser::ParseLibraryIncludeStmt() {
  auto* stmt = arena_.Create<IncludeStmt>();
  stmt->loc = CurrentLoc();
  Expect(TokenKind::kKwInclude);
  stmt->file_path = ParseFilePathSpec();
  if (stmt->file_path.empty()) {
    diag_.Error(CurrentLoc(), "expected file path after 'include'");
  }
  Expect(TokenKind::kSemicolon);
  return stmt;
}

// --- Bind directive (§23.11 / A.1.2) ---

BindDirective* Parser::ParseBindDirective() {
  auto* decl = arena_.Create<BindDirective>();
  decl->loc = CurrentLoc();
  Expect(TokenKind::kKwBind);

  // Parse target: hierarchical_identifier with optional constant_bit_select.
  decl->target = ParseDottedPath();
  if (Check(TokenKind::kLBracket)) {
    Consume();
    decl->target_bit_select = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  // Optional : bind_target_instance_list
  if (Match(TokenKind::kColon)) {
    do {
      decl->target_instances.push_back(ParseDottedPath());
      Expr* bit_sel = nullptr;
      if (Check(TokenKind::kLBracket)) {
        Consume();
        bit_sel = ParseExpr();
        Expect(TokenKind::kRBracket);
      }
      decl->target_instance_bit_selects.push_back(bit_sel);
    } while (Match(TokenKind::kComma));
  }

  // Parse bind_instantiation (module/interface/program/checker instantiation).
  auto mod_tok = ExpectIdentifier();
  decl->instantiation = ParseModuleInst(mod_tok);
  return decl;
}

// §18.5.1: out-of-block constraint —
//   [static] constraint [dynamic_override_specifiers] class::name { ... }
void Parser::ParseOutOfBlockConstraint(CompilationUnit* unit) {
  Match(TokenKind::kKwStatic);
  Expect(TokenKind::kKwConstraint);
  // Optional dynamic_override_specifiers: [:initial|:extends] [:final]
  if (Match(TokenKind::kColon)) {
    Match(TokenKind::kKwInitial) || Match(TokenKind::kKwExtends) ||
        Match(TokenKind::kKwFinal);
  }
  if (Match(TokenKind::kColon)) Match(TokenKind::kKwFinal);
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
    auto* udp = ParseUdpDecl();
    unit->udps.push_back(udp);
    known_udps_.insert(udp->name);
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

// anonymous_program: program ; { ... } endprogram (A.1.11)
bool Parser::TryParseAnonymousProgram(CompilationUnit* unit) {
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kSemicolon)) {
    lexer_.RestorePos(saved);
    return false;
  }
  Consume();
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    size_t before = unit->cu_items.size();
    ParseModuleItem(unit->cu_items);
    for (size_t i = before; i < unit->cu_items.size(); ++i) {
      unit->cu_items[i]->from_anonymous_program = true;
    }
  }
  Expect(TokenKind::kKwEndprogram);
  return true;
}

bool Parser::TryParsePrimaryTopLevel(CompilationUnit* unit) {
  if (Check(TokenKind::kKwExtern)) {
    ParseExternTopLevel(unit);
    return true;
  }
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseModuleDecl());
    return true;
  }
  if (Check(TokenKind::kKwPackage)) {
    unit->packages.push_back(ParsePackageDecl());
    return true;
  }
  if (IsAtClassDecl()) {
    unit->classes.push_back(ParseClassDecl());
    return true;
  }
  if (Check(TokenKind::kKwInterface)) {
    unit->interfaces.push_back(ParseInterfaceDecl());
    return true;
  }
  if (Check(TokenKind::kKwProgram)) {
    if (TryParseAnonymousProgram(unit)) return true;
    unit->programs.push_back(ParseProgramDecl());
    return true;
  }
  return false;
}

void Parser::ParseTopLevel(CompilationUnit* unit) {
  if (Match(TokenKind::kSemicolon)) return;  // null item
  auto top_attrs = ParseAttributes();        // consume optional (* ... *)
  auto udp_count = unit->udps.size();
  if (TryParsePrimaryTopLevel(unit)) {
    if (!top_attrs.empty()) {
      if (unit->udps.size() > udp_count) {
        unit->udps.back()->attrs = std::move(top_attrs);
      } else if (!unit->modules.empty()) {
        unit->modules.back()->attrs = std::move(top_attrs);
      }
    }
    return;
  }
  // §3.12.1: CU-scope typedef declaration.
  if (Check(TokenKind::kKwTypedef)) {
    unit->cu_items.push_back(ParseTypedef());
    return;
  }
  if (Check(TokenKind::kKwBind)) {
    unit->bind_directives.push_back(ParseBindDirective());
    return;
  }
  if (TryParseSecondaryTopLevel(unit)) {
    if (!top_attrs.empty() && unit->udps.size() > udp_count) {
      unit->udps.back()->attrs = std::move(top_attrs);
    }
    return;
  }
  if (TryParseCuScopeItem(unit)) return;
  diag_.Error(CurrentLoc(), "expected top-level declaration");
  Consume();
}

bool Parser::TryParseCuScopeItem(CompilationUnit* unit) {
  // §3.12.1: CU-scope localparam/parameter declarations.
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    std::vector<ModuleItem*> items;
    ParseParamDecl(items);
    for (auto* item : items) unit->cu_items.push_back(item);
    return true;
  }
  // §3.12.1: CU-scope import declarations.
  if (Check(TokenKind::kKwImport)) {
    std::vector<ModuleItem*> items;
    ParseImportDecl(items);
    for (auto* item : items) unit->cu_items.push_back(item);
    return true;
  }
  // §3.12.1: CU-scope data declarations (variables/nets).
  if (TryParseCuScopeDataDecl(unit)) return true;
  // CU-scope timeunit/timeprecision (§3.14.2.3 rule c)
  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParseTimeunitDecl(nullptr, unit);
    return true;
  }
  // extern_constraint_declaration: static constraint ... (A.1.10)
  if (Check(TokenKind::kKwStatic)) {
    ParseOutOfBlockConstraint(unit);
    return true;
  }
  return false;
}

// §3.12.1: Parse a data/net declaration at CU scope.
static bool IsCuScopeDataTypeKeyword(TokenKind tk) {
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
    case TokenKind::kKwVar:
    case TokenKind::kKwWire:
    case TokenKind::kKwTri:
    case TokenKind::kKwEvent:
    case TokenKind::kKwChandle:
      return true;
    default:
      return false;
  }
}

bool Parser::TryParseCuScopeDataDecl(CompilationUnit* unit) {
  if (!IsCuScopeDataTypeKeyword(CurrentToken().kind)) return false;
  std::vector<ModuleItem*> items;
  ParseDataDeclItem(items, 0, {});
  for (auto* item : items) unit->cu_items.push_back(item);
  return true;
}

void Parser::ParseExternTopLevel(CompilationUnit* unit) {
  Consume();  // extern
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseExternModuleDecl());
    return;
  }
  if (Check(TokenKind::kKwInterface)) {
    auto* decl = arena_.Create<ModuleDecl>();
    decl->decl_kind = ModuleDeclKind::kInterface;
    decl->is_extern = true;
    decl->range.start = CurrentLoc();
    Consume();  // interface
    Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);
    decl->name = Expect(TokenKind::kIdentifier).text;
    ParseParamsPortsAndSemicolon(*decl);
    unit->interfaces.push_back(decl);
    return;
  }
  if (Check(TokenKind::kKwProgram)) {
    auto* decl = arena_.Create<ModuleDecl>();
    decl->decl_kind = ModuleDeclKind::kProgram;
    decl->is_extern = true;
    decl->range.start = CurrentLoc();
    Consume();  // program
    Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);
    decl->name = Expect(TokenKind::kIdentifier).text;
    ParseParamsPortsAndSemicolon(*decl);
    unit->programs.push_back(decl);
    return;
  }
  if (Check(TokenKind::kKwPrimitive)) {
    auto* udp = ParseExternUdpDecl();
    unit->udps.push_back(udp);
    known_udps_.insert(udp->name);
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
  mod->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!mod->is_automatic) Match(TokenKind::kKwStatic);
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

  // Optional lifetime qualifier (§13.4.2)
  mod->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!mod->is_automatic) Match(TokenKind::kKwStatic);

  auto name_tok = ExpectIdentifier();
  mod->name = name_tok.text;
  mod->range.start = loc;

  ParseParamsPortsAndSemicolon(*mod);
  ParseModuleBody(*mod);
  Expect(TokenKind::kKwEndmodule);
  MatchEndLabel(mod->name);
  mod->range.end = CurrentLoc();
  return mod;
}

// Parse a single item inside a package body. Returns true if handled.
bool Parser::TryParsePackageBodyItem(std::vector<ModuleItem*>& items) {
  // anonymous_program: program ; { ... } endprogram (A.1.11)
  if (Check(TokenKind::kKwProgram)) {
    Consume();
    Expect(TokenKind::kSemicolon);
    while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
      if (Match(TokenKind::kSemicolon)) continue;
      size_t before = items.size();
      ParseModuleItem(items);
      for (size_t i = before; i < items.size(); ++i) {
        items[i]->from_anonymous_program = true;
      }
    }
    Expect(TokenKind::kKwEndprogram);
    return true;
  }
  // extern_constraint_declaration in package (A.1.11)
  if (Check(TokenKind::kKwConstraint)) {
    ParseOutOfBlockConstraint(nullptr);
    return true;
  }
  if (Check(TokenKind::kKwStatic)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kKwConstraint)) {
      lexer_.RestorePos(saved);
      ParseOutOfBlockConstraint(nullptr);
      return true;
    }
    lexer_.RestorePos(saved);
  }
  return false;
}

PackageDecl* Parser::ParsePackageDecl() {
  auto* pkg = arena_.Create<PackageDecl>();
  pkg->range.start = CurrentLoc();
  Expect(TokenKind::kKwPackage);

  // Optional lifetime qualifier (§26.2 / A.1.2)
  Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);

  pkg->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);
  while (!Check(TokenKind::kKwEndpackage) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;  // null item (A.1.11)
    // A specify block is only valid as a module item; reject it here before
    // the shared module-item dispatcher would silently accept it.
    if (Check(TokenKind::kKwSpecify)) {
      diag_.Error(CurrentLoc(),
                  "specify block must appear inside a module declaration");
      ParseSpecifyBlock();
      continue;
    }
    if (!TryParsePackageBodyItem(pkg->items)) {
      ParseModuleItem(pkg->items);
    }
  }
  Expect(TokenKind::kKwEndpackage);
  MatchEndLabel(pkg->name);
  pkg->range.end = CurrentLoc();
  return pkg;
}

// §11.12: Parse a single let port argument.
// A.2.12: let_port_item ::= {attribute_instance} let_formal_type
//         formal_port_identifier {variable_dimension} [= expression]
FunctionArg Parser::ParseLetArg() {
  FunctionArg arg;
  ParseAttributes();  // A.2.12: {attribute_instance}
  if (!Match(TokenKind::kKwUntyped)) {
    arg.data_type = ParseDataType();
  }
  arg.name = Expect(TokenKind::kIdentifier).text;
  ParseUnpackedDims(arg.unpacked_dims);
  if (Match(TokenKind::kEq)) {
    arg.default_value = ParseExpr();
  }
  return arg;
}

// §11.12: let declaration — let name(args) = expr;
// let_port_item ::= let_formal_type identifier {dim} [= expr]
// let_formal_type ::= data_type_or_implicit | untyped
ModuleItem* Parser::ParseLetDecl() {
  Consume();  // 'let'
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->loc = CurrentLoc();
  item->name = ExpectIdentifier().text;
  if (Check(TokenKind::kLParen)) {
    Consume();  // '('
    if (!Check(TokenKind::kRParen)) {
      item->func_args.push_back(ParseLetArg());
      while (Match(TokenKind::kComma)) {
        item->func_args.push_back(ParseLetArg());
      }
    }
    Expect(TokenKind::kRParen);
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

static void ApplyTimeUnit(ModuleDecl* mod, CompilationUnit* cu, bool is_unit,
                          TimeUnit tu) {
  if (mod) {
    if (is_unit) {
      mod->time_unit = tu;
      mod->has_timeunit = true;
    } else {
      mod->time_prec = tu;
      mod->has_timeprecision = true;
    }
  }
  if (cu) {
    if (is_unit) {
      cu->cu_time_unit = tu;
      cu->has_cu_timeunit = true;
    } else {
      cu->cu_time_prec = tu;
      cu->has_cu_timeprecision = true;
    }
  }
}

static void ApplyTimePrecision(ModuleDecl* mod, CompilationUnit* cu,
                               TimeUnit prec) {
  if (mod) {
    mod->time_prec = prec;
    mod->has_timeprecision = true;
  }
  if (cu) {
    cu->cu_time_prec = prec;
    cu->has_cu_timeprecision = true;
  }
}

void Parser::ParseTimeunitDecl(ModuleDecl* mod, CompilationUnit* cu) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  Consume();
  auto tok = Consume();
  TimeUnit tu = TimeUnit::kNs;
  TryParseTimeUnit(tok.text, tu);
  ApplyTimeUnit(mod, cu, is_unit, tu);
  if (Match(TokenKind::kSlash)) {
    auto prec_tok = Consume();
    TimeUnit prec = TimeUnit::kNs;
    TryParseTimeUnit(prec_tok.text, prec);
    // §3.14: Precision shall be at least as precise as the unit.
    if (static_cast<int>(prec) > static_cast<int>(tu)) {
      diag_.Error(prec_tok.loc,
                  "time precision is less precise than the time unit");
    }
    if (is_unit) ApplyTimePrecision(mod, cu, prec);
  }
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
