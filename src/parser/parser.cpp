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

  // Parse target: identifier (potentially hierarchical for form 2).
  decl->target = ParseDottedPath();

  // Optional : bind_target_instance_list
  if (Match(TokenKind::kColon)) {
    do {
      decl->target_instances.push_back(ParseDottedPath());
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

// anonymous_program: program ; { ... } endprogram (A.1.11)
bool Parser::TryParseAnonymousProgram() {
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kSemicolon)) {
    lexer_.RestorePos(saved);
    return false;
  }
  Consume();
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    std::vector<ModuleItem*> discard;
    ParseModuleItem(discard);
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
    if (TryParseAnonymousProgram()) return true;
    unit->programs.push_back(ParseProgramDecl());
    return true;
  }
  return false;
}

void Parser::ParseTopLevel(CompilationUnit* unit) {
  if (Match(TokenKind::kSemicolon)) return;  // null item
  ParseAttributes();                         // consume optional (* ... *)
  if (TryParsePrimaryTopLevel(unit)) return;
  if (Check(TokenKind::kKwTypedef)) {
    std::vector<ModuleItem*> discard;
    ParseModuleItem(discard);
    return;
  }
  if (Check(TokenKind::kKwBind)) {
    unit->bind_directives.push_back(ParseBindDirective());
    return;
  }
  if (TryParseSecondaryTopLevel(unit)) return;
  // extern_constraint_declaration: static constraint ... (A.1.10)
  if (Check(TokenKind::kKwStatic)) {
    ParseOutOfBlockConstraint(unit);
    return;
  }
  diag_.Error(CurrentLoc(), "expected top-level declaration");
  Consume();
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

// Parse a single item inside a package body. Returns true if handled.
bool Parser::TryParsePackageBodyItem(std::vector<ModuleItem*>& items) {
  // anonymous_program: program ; { ... } endprogram (A.1.11)
  if (Check(TokenKind::kKwProgram)) {
    Consume();
    Expect(TokenKind::kSemicolon);
    while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
      if (Match(TokenKind::kSemicolon)) continue;
      ParseModuleItem(items);
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
    if (!TryParsePackageBodyItem(pkg->items)) {
      ParseModuleItem(pkg->items);
    }
  }
  Expect(TokenKind::kKwEndpackage);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  pkg->range.end = CurrentLoc();
  return pkg;
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

// §11.12: Parse a single let port argument.
FunctionArg Parser::ParseLetArg() {
  FunctionArg arg;
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
    bool is_disable = Check(TokenKind::kKwDisable);
    lexer_.RestorePos(saved);
    if (is_clocking) {
      items.push_back(ParseClockingDecl());
      return true;
    }
    if (is_disable) {
      Consume();  // default
      Consume();  // disable
      Expect(TokenKind::kKwIff);
      auto* item = arena_.Create<ModuleItem>();
      item->kind = ModuleItemKind::kDefaultDisableIff;
      item->loc = CurrentLoc();
      item->init_expr = ParseExpr();
      Expect(TokenKind::kSemicolon);
      items.push_back(item);
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

static bool IsElabSeverityTask(TokenKind kind, std::string_view text) {
  return kind == TokenKind::kSystemIdentifier &&
         (text == "$fatal" || text == "$error" || text == "$warning" ||
          text == "$info");
}

bool Parser::TryParseDeclKeywordItem(std::vector<ModuleItem*>& items) {
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
  // extern_tf_declaration (A.1.6): extern method_prototype ;
  //                               | extern forkjoin task_prototype ;
  if (Check(TokenKind::kKwExtern)) {
    Consume();
    bool forkjoin = Match(TokenKind::kKwForkjoin);
    ModuleItem* item = nullptr;
    if (forkjoin || Check(TokenKind::kKwTask)) {
      item = ParseTaskDecl(/*prototype_only=*/true);
    } else {
      item = ParseFunctionDecl(/*prototype_only=*/true);
    }
    item->is_extern = true;
    item->is_forkjoin = forkjoin;
    items.push_back(item);
    return true;
  }
  return false;
}

bool Parser::TryParseMiscKeywordItem(std::vector<ModuleItem*>& items) {
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
    // A.2.2.1: interconnect implicit_data_type [signing] {packed_dimension}
    if (Match(TokenKind::kKwSigned)) {
      dtype.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
    return true;
  }
  return false;
}

bool Parser::TryParseKeywordItem(std::vector<ModuleItem*>& items) {
  if (TryParseDeclKeywordItem(items)) return true;
  if (TryParseMiscKeywordItem(items)) return true;
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
  // Nested interface declaration (non_port_module_item) — IsAtClassDecl
  // already ruled out 'interface class', so this is a nested interface.
  if (Check(TokenKind::kKwInterface)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseInterfaceDecl();
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

// A.1.4 non_port_module_item additions: elaboration severity tasks,
// nested module/program/interface declarations.
bool Parser::TryParseNonPortItem(std::vector<ModuleItem*>& items) {
  if (IsElabSeverityTask(CurrentToken().kind, CurrentToken().text)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kElabSystemTask;
    item->loc = CurrentLoc();
    item->init_expr = ParseExpr();
    Expect(TokenKind::kSemicolon);
    items.push_back(item);
    return true;
  }
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseModuleDecl();
    items.push_back(item);
    return true;
  }
  if (Check(TokenKind::kKwProgram)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseProgramDecl();
    items.push_back(item);
    return true;
  }
  // checker_or_generate_item_declaration: nested checker_declaration (A.1.8)
  if (Check(TokenKind::kKwChecker)) {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseCheckerDecl();
    items.push_back(item);
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
    ParseParamDecl(items);
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
  if (TryParseNonPortItem(items)) {
    AttachAttrs(items, before, attrs);
    return;
  }
  ParseDataDeclItem(items, before, attrs);
}

void Parser::ParseDataDeclItem(std::vector<ModuleItem*>& items, size_t before,
                               const std::vector<Attribute>& attrs) {
  // A.2.1.3: data_declaration ::= [const] [var] [lifetime] ...
  bool is_automatic = Match(TokenKind::kKwAutomatic);
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);
  // checker_or_generate_item_declaration: [rand] data_declaration (A.1.8)
  bool is_rand = Match(TokenKind::kKwRand);
  ParseTypedItemOrInst(items);
  for (size_t i = before; i < items.size(); ++i) {
    if (is_rand) items[i]->is_rand = true;
    if (is_automatic) items[i]->is_automatic = true;
    if (is_static) items[i]->is_static = true;
  }
  AttachAttrs(items, before, attrs);
}

bool Parser::TryParseTypeRef(std::vector<ModuleItem*>& items) {
  // §6.23 / A.2.2.1: type_reference used as data_type in declaration.
  if (!Check(TokenKind::kKwType)) return false;
  Consume();  // type
  Expect(TokenKind::kLParen);
  auto* type_expr = ParseExpr();
  Expect(TokenKind::kRParen);
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = CurrentLoc();
  item->data_type.type_ref_expr = type_expr;
  item->name = ExpectIdentifier().text;
  ParseUnpackedDims(item->unpacked_dims);
  Expect(TokenKind::kSemicolon);
  items.push_back(item);
  return true;
}

void Parser::ParseTypedItemOrInst(std::vector<ModuleItem*>& items) {
  // Handle 'var' prefix: var type(expr) name; or var data_type name; (§6.8)
  if (Match(TokenKind::kKwVar)) {
    if (TryParseTypeRef(items)) return;
    auto dtype = ParseDataType();
    ParseVarDeclList(items, dtype);
    return;
  }
  if (TryParseTypeRef(items)) return;
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
  // A.2.2.1: implicit_data_type with signing/dims is a real type
  if (dtype.kind != DataTypeKind::kImplicit || dtype.packed_dim_left ||
      dtype.is_signed || dtype.is_const) {
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
