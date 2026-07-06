#include "parser/parser.h"

#include "common/types.h"
#include "parser/time_resolve.h"

namespace delta {

namespace {
// §A.1.11: anonymous_program_item is a closed set (task, function, class,
// interface-class, covergroup, and class-constructor declarations, plus the
// null item). Unlike a named program, an anonymous program may not contain net
// or variable declarations, so reject any that appear directly in its body.
void CheckAnonymousProgramItem(DiagEngine& diag, ModuleItem* item) {
  if (item->kind == ModuleItemKind::kNetDecl ||
      item->kind == ModuleItemKind::kVarDecl) {
    diag.Error(item->loc,
               "a net or variable declaration is not allowed in an anonymous "
               "program");
  }
}

// Each top-level design element defaults to the "work" library unless one was
// assigned during parsing. Apply that default to every element in a collection.
template <typename Collection>
void DefaultLibraryToWork(Collection& elements) {
  for (auto* element : elements) {
    if (element->library.empty()) element->library = "work";
  }
}

// Snapshot of the compilation unit's timeunit/timeprecision state captured
// before a compilation-unit-scope timeunit declaration is parsed, used to
// detect mismatches and out-of-order declarations afterward.
struct CuTimeunitSnapshot {
  bool was_unit_set = false;
  bool was_prec_set = false;
  TimeUnit old_unit = TimeUnit::kNs;
  int old_unit_mag = 0;
  TimeUnit old_prec = TimeUnit::kNs;
  int old_prec_mag = 0;
  bool has_other_items = false;
};

CuTimeunitSnapshot CaptureCuTimeunitState(const CompilationUnit* unit) {
  CuTimeunitSnapshot snap;
  snap.was_unit_set = unit->has_cu_timeunit;
  snap.was_prec_set = unit->has_cu_timeprecision;
  snap.old_unit = unit->cu_time_unit;
  snap.old_unit_mag = unit->cu_time_unit_magnitude;
  snap.old_prec = unit->cu_time_prec;
  snap.old_prec_mag = unit->cu_time_prec_magnitude;
  snap.has_other_items = !unit->modules.empty() || !unit->packages.empty() ||
                         !unit->interfaces.empty() || !unit->programs.empty() ||
                         !unit->classes.empty() || !unit->udps.empty() ||
                         !unit->checkers.empty() || !unit->configs.empty() ||
                         !unit->cu_items.empty();
  return snap;
}

void CheckCuTimeunitConsistency(DiagEngine& diag, SourceLoc loc,
                                const CuTimeunitSnapshot& snap,
                                const CompilationUnit* unit) {
  if (unit->has_cu_timeunit && !snap.was_unit_set && snap.has_other_items) {
    diag.Error(loc,
               "timeunit as a later item requires a matching prior "
               "declaration in the same time scope");
  } else if (snap.was_unit_set &&
             (unit->cu_time_unit != snap.old_unit ||
              unit->cu_time_unit_magnitude != snap.old_unit_mag)) {
    diag.Error(loc, "timeunit does not match prior declaration");
  }
  if (unit->has_cu_timeprecision && !snap.was_prec_set &&
      snap.has_other_items) {
    diag.Error(loc,
               "timeprecision as a later item requires a matching prior "
               "declaration in the same time scope");
  } else if (snap.was_prec_set &&
             (unit->cu_time_prec != snap.old_prec ||
              unit->cu_time_prec_magnitude != snap.old_prec_mag)) {
    diag.Error(loc, "timeprecision does not match prior declaration");
  }
}
}  // namespace

Parser::Parser(Lexer& lexer, Arena& arena, DiagEngine& diag)
    : lexer_(lexer), arena_(arena), diag_(diag) {
  known_types_.insert("process");

  known_types_.insert("semaphore");
  known_types_.insert("mailbox");

  known_types_.insert("weak_reference");
}

Token Parser::CurrentToken() { return lexer_.Peek(); }
bool Parser::Check(TokenKind kind) {
  auto cur = CurrentToken().kind;
  if (kind == TokenKind::kIdentifier) {
    return cur == TokenKind::kIdentifier ||
           cur == TokenKind::kEscapedIdentifier;
  }
  return cur == kind;
}
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

std::string_view Parser::ArenaCopy(std::string_view text) {
  auto* buf = static_cast<char*>(arena_.Allocate(text.size(), 1));
  std::copy_n(text.data(), text.size(), buf);
  return {buf, text.size()};
}

std::string_view Parser::ParseDottedPath() {
  auto first = ExpectIdentifier().text;
  std::string path(first);
  while (Match(TokenKind::kDot)) {
    path.push_back('.');
    auto next = ExpectIdentifier().text;
    path.append(next.data(), next.size());
  }
  return ArenaCopy(path);
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

void Parser::SynchronizeWithProgress() {
  auto before = lexer_.SavePos().pos;
  Synchronize();
  if (!AtEnd() && lexer_.SavePos().pos == before) Consume();
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

std::vector<Attribute> Parser::ParseAttributes() {
  std::vector<Attribute> attrs;
  while (Check(TokenKind::kAttrStart)) {
    Consume();
    do {
      Attribute attr;

      auto tok = ExpectIdentifier();
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

  DefaultLibraryToWork(unit->modules);
  DefaultLibraryToWork(unit->interfaces);
  DefaultLibraryToWork(unit->programs);
  DefaultLibraryToWork(unit->udps);
  DefaultLibraryToWork(unit->packages);
  DefaultLibraryToWork(unit->configs);
  return unit;
}

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
  return ArenaCopy(tok.text);
}

LibraryDecl* Parser::ParseLibraryDecl() {
  auto* decl = arena_.Create<LibraryDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwLibrary);
  // The library name view must outlive the throwaway SourceManager used to
  // parse this map file, so copy it into the long-lived parser arena.
  decl->name = ArenaCopy(Expect(TokenKind::kIdentifier).text);

  auto path = ParseFilePathSpec();
  if (path.empty()) {
    diag_.Error(CurrentLoc(), "expected at least one file path in library");
    Synchronize();
    return decl;
  }
  decl->file_paths.push_back(path);

  while (Match(TokenKind::kComma)) {
    decl->file_paths.push_back(ParseFilePathSpec());
  }

  if (Check(TokenKind::kMinus)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kKwIncdir)) {
      Consume();
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

BindDirective* Parser::ParseBindDirective() {
  auto* decl = arena_.Create<BindDirective>();
  decl->loc = CurrentLoc();
  Expect(TokenKind::kKwBind);

  decl->target = ParseDottedPath();
  if (Check(TokenKind::kLBracket)) {
    Consume();
    decl->target_bit_select = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

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

  auto mod_tok = ExpectIdentifier();
  decl->instantiation = ParseModuleInst(mod_tok);
  return decl;
}

void Parser::ParseOutOfBlockConstraint(CompilationUnit* unit) {
  // 18.5.1: external constraint block, declared outside its enclosing class
  // with the class scope resolution operator. Record the class/name pair and
  // its location so elaboration can pair it with a prototype and check its
  // placement.
  SourceLoc loc = CurrentLoc();
  // 18.5.10: an external constraint block may be qualified 'static'. Record
  // whether the keyword is present so elaboration can check that it agrees with
  // the completing prototype's qualification.
  bool is_static = Match(TokenKind::kKwStatic);
  Expect(TokenKind::kKwConstraint);

  // 18.5.2: capture the dynamic override specifiers so elaboration can check
  // that they match those on the completing constraint prototype.
  bool is_initial = false;
  bool is_extends = false;
  bool is_final = false;
  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwInitial)) {
      is_initial = true;
    } else if (Match(TokenKind::kKwExtends)) {
      is_extends = true;
    } else if (Match(TokenKind::kKwFinal)) {
      is_final = true;
    }
  }
  if (Match(TokenKind::kColon) && Match(TokenKind::kKwFinal)) is_final = true;
  std::string_view class_name = ExpectIdentifier().text;
  Expect(TokenKind::kColonColon);
  std::string_view constraint_name = ExpectIdentifier().text;
  Expect(TokenKind::kLBrace);
  // 18.5.1: capture the block's relations so elaboration can complete the
  // matching prototype with them. The body is scanned exactly like an in-class
  // constraint block, using a scratch member to collect the relations.
  auto* body = arena_.Create<ClassMember>();
  body->kind = ClassMemberKind::kConstraint;
  ScanConstraintBodyRelations(body);
  if (unit) {
    ExternalConstraintBlock ext{class_name, constraint_name, loc,
                                is_initial, is_extends,      is_final,
                                is_static};
    ext.constraint_exprs = std::move(body->constraint_exprs);
    unit->external_constraints.push_back(std::move(ext));
  }
}

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

bool Parser::TryParseAnonymousProgram(CompilationUnit* unit) {
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kSemicolon)) {
    lexer_.RestorePos(saved);
    return false;
  }
  Consume();
  bool prev_anon = in_anonymous_program_;
  in_anonymous_program_ = true;
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    size_t before = unit->cu_items.size();
    ParseModuleItem(unit->cu_items);
    for (size_t i = before; i < unit->cu_items.size(); ++i) {
      unit->cu_items[i]->from_anonymous_program = true;
      CheckAnonymousProgramItem(diag_, unit->cu_items[i]);
    }
  }
  in_anonymous_program_ = prev_anon;
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
  current_compilation_unit_ = unit;
  if (Match(TokenKind::kSemicolon)) return;
  auto top_attrs = ParseAttributes();
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
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    std::vector<ModuleItem*> items;
    in_cu_scope_param_ = true;
    ParseParamDecl(items);
    in_cu_scope_param_ = false;
    for (auto* item : items) unit->cu_items.push_back(item);
    return true;
  }

  if (Check(TokenKind::kKwImport)) {
    std::vector<ModuleItem*> items;
    ParseImportDecl(items);
    for (auto* item : items) unit->cu_items.push_back(item);
    return true;
  }

  if (Check(TokenKind::kKwLet)) {
    unit->cu_items.push_back(ParseLetDecl());
    return true;
  }

  if (TryParseCuScopeDataDecl(unit)) return true;

  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    CuTimeunitSnapshot snap = CaptureCuTimeunitState(unit);
    auto loc = CurrentLoc();
    ParseTimeunitDecl(nullptr, unit);
    CheckCuTimeunitConsistency(diag_, loc, snap, unit);
    return true;
  }

  if (Check(TokenKind::kKwStatic)) {
    ParseOutOfBlockConstraint(unit);
    return true;
  }

  if (Check(TokenKind::kKwSequence)) {
    unit->cu_items.push_back(ParseSequenceDecl());
    return true;
  }

  if (Check(TokenKind::kKwProperty)) {
    unit->cu_items.push_back(ParsePropertyDecl());
    return true;
  }

  return false;
}

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
  Consume();
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseExternModuleDecl());
    return;
  }
  if (Check(TokenKind::kKwInterface)) {
    auto* decl = arena_.Create<ModuleDecl>();
    decl->decl_kind = ModuleDeclKind::kInterface;
    decl->is_extern = true;
    decl->range.start = CurrentLoc();
    Consume();
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
    Consume();
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

bool Parser::TryParsePackageBodyItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwProgram)) {
    Consume();
    Expect(TokenKind::kSemicolon);
    bool prev_anon = in_anonymous_program_;
    in_anonymous_program_ = true;
    while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
      if (Match(TokenKind::kSemicolon)) continue;
      size_t before = items.size();
      ParseModuleItem(items);
      for (size_t i = before; i < items.size(); ++i) {
        items[i]->from_anonymous_program = true;
        CheckAnonymousProgramItem(diag_, items[i]);
      }
    }
    in_anonymous_program_ = prev_anon;
    Expect(TokenKind::kKwEndprogram);
    return true;
  }

  if (Check(TokenKind::kKwConstraint)) {
    ParseOutOfBlockConstraint(current_compilation_unit_);
    return true;
  }
  if (Check(TokenKind::kKwStatic)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kKwConstraint)) {
      lexer_.RestorePos(saved);
      ParseOutOfBlockConstraint(current_compilation_unit_);
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

  if (Match(TokenKind::kKwAutomatic)) {
    pkg->is_automatic = true;
  } else {
    Match(TokenKind::kKwStatic);
  }

  pkg->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);

  auto* prev_package = current_package_;
  current_package_ = pkg;
  ++package_body_depth_;
  while (!Check(TokenKind::kKwEndpackage) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;

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
  --package_body_depth_;
  current_package_ = prev_package;
  Expect(TokenKind::kKwEndpackage);
  MatchEndLabel(pkg->name);
  pkg->range.end = CurrentLoc();
  return pkg;
}

FunctionArg Parser::ParseLetArg() {
  FunctionArg arg;
  ParseAttributes();
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

ModuleItem* Parser::ParseLetDecl() {
  Consume();
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->loc = CurrentLoc();
  item->name = ExpectIdentifier().text;
  if (Check(TokenKind::kLParen)) {
    Consume();
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
  Consume();
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kVarDecl;
    item->loc = CurrentLoc();
    item->name = Expect(TokenKind::kIdentifier).text;
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

namespace {
// The three SystemVerilog scopes (§3.14.2) whose timeunit/timeprecision a
// single "timeunit"/"timeprecision" declaration can update: an enclosing
// module, the compilation unit, and an enclosing package. Any subset may be
// null.
struct TimeScopeTargets {
  ModuleDecl* mod;
  CompilationUnit* cu;
  PackageDecl* pkg;
};

// The already-parsed "unit" part of a timeunit/timeprecision declaration
// (§3.14.2): whether it is a timeunit (vs timeprecision) declaration, whether
// the unit token was the literal 'step', and the parsed unit value.
struct TimeunitDecl {
  bool is_unit;
  bool unit_is_step;
  TimeUnit tu;
  int mag;
};

// Apply a timeunit/timeprecision setting to a single scope (module, package, or
// any type whose timeunit fields are named time_unit/time_prec). The
// compilation-unit scope uses differently named fields and is handled
// separately by ApplyCuTimeUnit.
template <typename Scope>
void ApplyScopeTimeUnit(Scope* scope, bool is_unit, TimeUnit tu, int mag) {
  if (!scope) return;
  if (is_unit) {
    scope->time_unit = tu;
    scope->time_unit_magnitude = mag;
    scope->has_timeunit = true;
  } else {
    scope->time_prec = tu;
    scope->time_prec_magnitude = mag;
    scope->has_timeprecision = true;
  }
}

void ApplyCuTimeUnit(CompilationUnit* cu, bool is_unit, TimeUnit tu, int mag) {
  if (!cu) return;
  if (is_unit) {
    cu->cu_time_unit = tu;
    cu->cu_time_unit_magnitude = mag;
    cu->has_cu_timeunit = true;
  } else {
    cu->cu_time_prec = tu;
    cu->cu_time_prec_magnitude = mag;
    cu->has_cu_timeprecision = true;
  }
}
}  // namespace

static void ApplyTimeUnit(const TimeScopeTargets& targets,
                          const TimeunitDecl& decl) {
  ApplyScopeTimeUnit(targets.mod, decl.is_unit, decl.tu, decl.mag);
  ApplyCuTimeUnit(targets.cu, decl.is_unit, decl.tu, decl.mag);
  ApplyScopeTimeUnit(targets.pkg, decl.is_unit, decl.tu, decl.mag);
}

static void ApplyTimePrecision(const TimeScopeTargets& targets, TimeUnit prec,
                               int mag) {
  if (targets.mod) {
    targets.mod->time_prec = prec;
    targets.mod->time_prec_magnitude = mag;
    targets.mod->has_timeprecision = true;
  }
  if (targets.cu) {
    targets.cu->cu_time_prec = prec;
    targets.cu->cu_time_prec_magnitude = mag;
    targets.cu->has_cu_timeprecision = true;
  }
  if (targets.pkg) {
    targets.pkg->time_prec = prec;
    targets.pkg->time_prec_magnitude = mag;
    targets.pkg->has_timeprecision = true;
  }
}

namespace {
// Validate the precision side of a "timeunit <unit> / <precision>" declaration
// (its token already consumed and known not to be 'step'), reporting a bad
// literal or a precision coarser than the unit, then store it when the
// declaration is a timeunit. Mirrors the inline logic it replaces exactly.
void ParsePrecisionFromToken(DiagEngine& diag, Token prec_tok,
                             const TimeunitDecl& decl,
                             const TimeScopeTargets& targets) {
  TimeUnit prec = TimeUnit::kNs;
  int prec_mag = 1;
  if (!TryParseTimeMagnitudeAndUnit(prec_tok.text, prec_mag, prec)) {
    diag.Error(prec_tok.loc,
               "time literal must use magnitude 1, 10, or 100 and unit "
               "s/ms/us/ns/ps/fs");
  }

  if (!decl.unit_is_step && EffectiveTimeOrder(prec, prec_mag) >
                                EffectiveTimeOrder(decl.tu, decl.mag)) {
    diag.Error(prec_tok.loc,
               "time precision is less precise than the time unit");
  }
  if (decl.is_unit) ApplyTimePrecision(targets, prec, prec_mag);
}
}  // namespace

void Parser::ParseTimeunitDecl(ModuleDecl* mod, CompilationUnit* cu,
                               PackageDecl* pkg) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  Consume();
  auto tok = Consume();
  TimeUnit tu = TimeUnit::kNs;
  int mag = 1;
  bool unit_is_step =
      Check(TokenKind::kIdentifier) && CurrentToken().text == "step";
  TimeScopeTargets targets{mod, cu, pkg};
  if (unit_is_step) {
    diag_.Error(
        tok.loc,
        "step cannot be used to set or modify the time unit or precision");
    Consume();
  } else {
    if (!TryParseTimeMagnitudeAndUnit(tok.text, mag, tu)) {
      diag_.Error(tok.loc,
                  "time literal must use magnitude 1, 10, or 100 and unit "
                  "s/ms/us/ns/ps/fs");
    }
    ApplyTimeUnit(targets, TimeunitDecl{is_unit, unit_is_step, tu, mag});
  }
  if (Match(TokenKind::kSlash)) {
    auto prec_tok = Consume();
    bool prec_is_step =
        Check(TokenKind::kIdentifier) && CurrentToken().text == "step";
    if (prec_is_step) {
      diag_.Error(
          prec_tok.loc,
          "step cannot be used to set or modify the time unit or precision");
      Consume();
    } else {
      ParsePrecisionFromToken(diag_, prec_tok,
                              TimeunitDecl{is_unit, unit_is_step, tu, mag},
                              targets);
    }
  }
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
