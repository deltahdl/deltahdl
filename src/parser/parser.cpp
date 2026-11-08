#include "parser/parser.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <tuple>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser_fsm.h"
#include "parser/parser_token_skips.h"
#include "parser/parser_type_name_scope.h"
#include "parser/scope_prefix_record.h"
#include "parser/scope_type_names.h"

namespace delta {

namespace {
bool IsAnonymousProgramItemKind(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kClassDecl:
    case ModuleItemKind::kCovergroupDecl:
      return true;
    default:
      return false;
  }
}

void FilterAnonymousProgramItems(DiagEngine& diag,
                                 std::vector<ModuleItem*>& items,
                                 size_t before) {
  size_t kept = before;
  for (size_t i = before; i < items.size(); ++i) {
    ModuleItem* item = items[i];
    if (!IsAnonymousProgramItemKind(item->kind) || item->is_extern) {
      diag.Error(item->loc, kAnonymousProgramItemsMessage, Subclause("A.1.11"));
      continue;
    }
    item->from_anonymous_program = true;
    items[kept++] = item;
  }
  items.resize(kept);
}

template <typename Collection>
void DefaultLibraryToWork(Collection& elements) {
  for (auto* element : elements) {
    if (element->library.empty()) element->library = "work";
  }
}

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
                         !unit->cu_items.empty() || unit->has_read_cu_item;
  return snap;
}

void CheckCuTimeunitConsistency(DiagEngine& diag, SourceLoc loc,
                                const CuTimeunitSnapshot& snap,
                                const CompilationUnit* unit) {
  if (unit->has_cu_timeunit && !snap.was_unit_set && snap.has_other_items) {
    diag.Error(loc,
               "timeunit as a later item requires a matching prior "
               "declaration in the same time scope",
               Subclause("3.14.2.2"));
  } else if (snap.was_unit_set &&
             (unit->cu_time_unit != snap.old_unit ||
              unit->cu_time_unit_magnitude != snap.old_unit_mag)) {
    diag.Error(loc, "timeunit does not match prior declaration",
               Subclause("3.14.2.2"));
  }
  if (unit->has_cu_timeprecision && !snap.was_prec_set &&
      snap.has_other_items) {
    diag.Error(loc,
               "timeprecision as a later item requires a matching prior "
               "declaration in the same time scope",
               Subclause("3.14.2.2"));
  } else if (snap.was_prec_set &&
             (unit->cu_time_prec != snap.old_prec ||
              unit->cu_time_prec_magnitude != snap.old_prec_mag)) {
    diag.Error(loc, "timeprecision does not match prior declaration",
               Subclause("3.14.2.2"));
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

Token Parser::Consume() {
  Token tok = lexer_.Next();
  scope_prefixes_.Read(tok, known_types_);
  return tok;
}

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
  auto first = ExpectIdentifier(Subclause("23.6")).text;
  std::string path(first);
  while (Match(TokenKind::kDot)) {
    path.push_back('.');
    auto next = ExpectIdentifier(Subclause("23.6")).text;
    path.append(next.data(), next.size());
  }
  return ArenaCopy(path);
}

Token Parser::Expect(TokenKind kind, Subclause subclause) {
  if (Check(kind)) {
    return Consume();
  }
  auto tok = CurrentToken();
  diag_.Error(tok.loc,
              "expected " + std::string(TokenKindName(kind)) + ", got " +
                  std::string(TokenKindName(tok.kind)),
              subclause);
  return tok;
}

bool Parser::ReportedAtEnd(size_t first_report) {
  const SourceLoc kEnd = CurrentLoc();
  const auto kAtEnd =
      std::tuple(DiagSeverity::kError, kEnd.file_id, kEnd.line, kEnd.column);
  const auto& reports = diag_.Diagnostics();
  return std::any_of(
      std::next(reports.begin(), static_cast<std::ptrdiff_t>(first_report)),
      reports.end(), [&](const Diagnostic& d) {
        return std::tuple(d.severity, d.loc.file_id, d.loc.line,
                          d.loc.column) == kAtEnd;
      });
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

      auto tok = ExpectIdentifier(Subclause("5.12"));
      attr.name = tok.text;
      attr.loc = tok.loc;
      if (Match(TokenKind::kEq)) {
        attr.value = ParseExpr();
      }
      attrs.push_back(attr);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kAttrEnd, Subclause("5.12"));
  }
  return attrs;
}

void Parser::AttachAttrs(std::vector<ModuleItem*>& items, size_t before,
                         const std::vector<Attribute>& attrs) {
  if (attrs.empty()) return;
  for (size_t i = before; i < items.size(); ++i) {
    items[i]->attrs = attrs;
    if (items[i]->class_decl != nullptr) items[i]->class_decl->attrs = attrs;
  }
}

void Parser::AdoptCompilationUnitScope(const CompilationUnitScopeNames& names) {
  AdoptTypeNames(names.own);
  package_types_.insert(names.packages.begin(), names.packages.end());
  class_types_.insert(names.classes.begin(), names.classes.end());
}

CompilationUnitScopeNames Parser::CompilationUnitScope() const {
  return CompilationUnitScopeNames{
      ScopeTypeNames{known_types_, known_nettypes_, known_udps_},
      package_types_, class_types_};
}

CompilationUnit* Parser::Parse() {
  auto* unit = arena_.Create<CompilationUnit>();
  const size_t kFirstReport = diag_.Diagnostics().size();
  while (!AtEnd()) {
    ParseTopLevel(unit);
  }
  ended_inside_declaration_ = ReportedAtEnd(kFirstReport);

  DefaultLibraryToWork(unit->modules);
  DefaultLibraryToWork(unit->interfaces);
  DefaultLibraryToWork(unit->programs);
  DefaultLibraryToWork(unit->udps);
  DefaultLibraryToWork(unit->packages);
  DefaultLibraryToWork(unit->configs);
  unit->triggered_names = std::move(triggered_names_);
  unit->time_literals = std::move(time_literals_);
  unit->scope_prefixes = scope_prefixes_.Take();
  unit->dotted_escaped_names = lexer_.DottedEscapedNames();
  BindFsmPragmas(lexer_, *unit);
  return unit;
}

void Parser::RecordTriggeredRead(const Expr* base) {
  if (base->kind == ExprKind::kCall) {
    triggered_names_.insert(base->callee);
  } else if (base->kind == ExprKind::kMemberAccess) {
    triggered_names_.insert(base->rhs->text);
  } else {
    triggered_names_.insert(base->text);
  }
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
                  "config declaration, or ';'",
                  Subclause("33.3.1"));
      Consume();
    }
  }
  return unit;
}

Token Parser::ParseFilePathSpec() {
  auto tok = lexer_.NextFilePathSpec();
  if (tok.kind == TokenKind::kEof) {
    diag_.Error(CurrentLoc(), "expected file path specification",
                Subclause("33.3.1"));
    return tok;
  }
  tok.text = ArenaCopy(tok.text);
  return tok;
}

SourceLoc Parser::ParseFilePathSpecList(std::vector<std::string_view>& paths) {
  do {
    auto tok = ParseFilePathSpec();
    if (tok.text == "-incdir") return tok.loc;
    if (tok.kind != TokenKind::kEof) paths.push_back(tok.text);
  } while (Match(TokenKind::kComma));
  return SourceLoc::None();
}

bool Parser::MatchIncdirOption() {
  if (!Check(TokenKind::kMinus)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  if (Match(TokenKind::kKwIncdir)) return true;
  lexer_.RestorePos(saved);
  return false;
}

LibraryDecl* Parser::ParseLibraryDecl() {
  auto* decl = arena_.Create<LibraryDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwLibrary, Subclause("33.3.1"));
  decl->name =
      ArenaCopy(Expect(TokenKind::kIdentifier, Subclause("33.3.1")).text);

  SourceLoc incdir_loc = ParseFilePathSpecList(decl->file_paths);
  bool has_incdir = incdir_loc.IsValid();
  if (has_incdir) {
    diag_.Error(incdir_loc, "library names its file paths before -incdir",
                Subclause("A.1.1"));
  } else if (decl->file_paths.empty()) {
    diag_.Error(CurrentLoc(), "expected at least one file path in library",
                Subclause("33.3.1"));
    Synchronize();
    return decl;
  } else {
    has_incdir = MatchIncdirOption();
  }

  if (has_incdir) {
    SourceLoc again = ParseFilePathSpecList(decl->incdir_paths);
    while (again.IsValid()) {
      diag_.Error(again,
                  "-incdir is written once, its directories after it "
                  "separated by commas",
                  Subclause("A.1.1"));
      again = ParseFilePathSpecList(decl->incdir_paths);
    }
  }

  Expect(TokenKind::kSemicolon, Subclause("33.3.1"));
  decl->range.end = CurrentLoc();
  return decl;
}

IncludeStmt* Parser::ParseLibraryIncludeStmt() {
  auto* stmt = arena_.Create<IncludeStmt>();
  stmt->loc = CurrentLoc();
  Expect(TokenKind::kKwInclude, Subclause("33.3.2"));
  stmt->file_path = ParseFilePathSpec().text;
  if (stmt->file_path.empty()) {
    diag_.Error(CurrentLoc(), "expected file path after 'include'",
                Subclause("33.3.1"));
  }
  Expect(TokenKind::kSemicolon, Subclause("33.3.2"));
  return stmt;
}

void Parser::ParseOutOfBlockConstraint(
    CompilationUnit* unit, const std::vector<ModuleItem*>* scope_items) {
  SourceLoc loc = CurrentLoc();
  bool is_static = Match(TokenKind::kKwStatic);
  Expect(TokenKind::kKwConstraint, Subclause("18.5.1"));

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
  std::string_view class_name = ExpectIdentifier(Subclause("18.5.1")).text;
  Expect(TokenKind::kColonColon, Subclause("18.5.1"));
  std::string_view constraint_name = ExpectIdentifier(Subclause("18.5.1")).text;
  Expect(TokenKind::kLBrace, Subclause("18.5.1"));
  auto* body = arena_.Create<ClassMember>();
  body->kind = ClassMemberKind::kConstraint;
  ScanConstraintBodyRelations(body, false);
  if (unit) {
    ExternalConstraintBlock ext{
        class_name, constraint_name, loc,  is_initial, is_extends,
        is_final,   is_static,       body, scope_items};
    unit->external_constraints.push_back(ext);
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
    ParseOutOfBlockConstraint(unit, nullptr);
    return true;
  }
  if (Check(TokenKind::kKwCovergroup)) {
    ParseCovergroupDecl(unit->cu_items);
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
    FilterAnonymousProgramItems(diag_, unit->cu_items, before);
  }
  in_anonymous_program_ = prev_anon;
  Expect(TokenKind::kKwEndprogram, Subclause("24.6"));
  return true;
}

bool Parser::TryParsePrimaryTopLevel(CompilationUnit* unit) {
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

namespace {

struct TopLevelSizes {
  size_t udps;
  size_t modules;
  size_t interfaces;
  size_t programs;
  size_t classes;
};

TopLevelSizes SizesOf(const CompilationUnit& unit) {
  return {unit.udps.size(), unit.modules.size(), unit.interfaces.size(),
          unit.programs.size(), unit.classes.size()};
}

std::vector<Attribute>* AttributesOfNewest(CompilationUnit& unit,
                                           const TopLevelSizes& before) {
  if (unit.udps.size() > before.udps) return &unit.udps.back()->attrs;
  if (unit.modules.size() > before.modules) return &unit.modules.back()->attrs;
  if (unit.interfaces.size() > before.interfaces) {
    return &unit.interfaces.back()->attrs;
  }
  if (unit.programs.size() > before.programs) {
    return &unit.programs.back()->attrs;
  }
  if (unit.classes.size() > before.classes) return &unit.classes.back()->attrs;
  return nullptr;
}

}  // namespace

void Parser::ParseTopLevel(CompilationUnit* unit) {
  current_compilation_unit_ = unit;
  if (NoteItemAndMatchNull(unit->has_read_cu_item)) return;
  auto top_attrs = ParseAttributes();
  if (Check(TokenKind::kKwExtern)) {
    if (!top_attrs.empty()) {
      diag_.Error(top_attrs.front().loc,
                  "an extern declaration's attribute instances are written "
                  "after 'extern', not before it",
                  Subclause("A.1.2"));
    }
    ParseExternTopLevel(unit);
    return;
  }
  const TopLevelSizes kBefore = SizesOf(*unit);
  if (TryParsePrimaryTopLevel(unit)) {
    if (std::vector<Attribute>* attrs = AttributesOfNewest(*unit, kBefore)) {
      *attrs = std::move(top_attrs);
    }
    return;
  }

  if (TryParseCuTypeDeclaration(unit)) return;
  if (TryParseUnitBindDirective(unit)) return;
  if (TryParseSecondaryTopLevel(unit)) {
    if (std::vector<Attribute>* attrs = AttributesOfNewest(*unit, kBefore)) {
      *attrs = std::move(top_attrs);
    }
    return;
  }
  if (TryParseCuScopeItem(unit)) return;
  ReportUnexpectedTopLevelToken();
}

bool Parser::TryParseCuTypeDeclaration(CompilationUnit* unit) {
  if (Check(TokenKind::kKwTypedef)) {
    unit->cu_items.push_back(ParseTypedef());
    return true;
  }
  if (Check(TokenKind::kKwNettype)) {
    unit->cu_items.push_back(ParseNettypeDecl());
    return true;
  }
  return false;
}

void Parser::ReportUnexpectedTopLevelToken() {
  if (AtClockingDecl()) {
    RejectClockingDecl(
        "a clocking block cannot stand at the top level of a compilation unit");
    return;
  }
  diag_.Error(CurrentLoc(), "expected top-level declaration",
              Subclause("3.12.1"));
  Consume();
}

bool Parser::TryParseCuImportOrExportDecl(CompilationUnit* unit) {
  const bool kIsImport = Check(TokenKind::kKwImport);
  if (!kIsImport && !Check(TokenKind::kKwExport)) return false;
  std::vector<ModuleItem*> items;
  if (kIsImport) {
    ParseImportDecl(items);
  } else {
    ParseExportDecl(items);
  }
  for (auto* item : items) unit->cu_items.push_back(item);
  return true;
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

  if (TryParseCuImportOrExportDecl(unit)) return true;

  if (Check(TokenKind::kKwLet)) {
    unit->cu_items.push_back(ParseLetDecl());
    return true;
  }

  if (Check(TokenKind::kKwStatic) && StaticOpensConstraint()) {
    ParseOutOfBlockConstraint(unit, nullptr);
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

void Parser::ParseExternTopLevel(CompilationUnit* unit) {
  SourceLoc extern_loc = CurrentLoc();
  Consume();
  std::vector<Attribute> attrs = ParseAttributes();
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    unit->modules.push_back(ParseExternModuleDecl());
    unit->modules.back()->attrs = std::move(attrs);
    return;
  }
  if (Check(TokenKind::kKwInterface)) {
    unit->interfaces.push_back(ParseExternInterfaceOrProgramDecl());
    unit->interfaces.back()->attrs = std::move(attrs);
    return;
  }
  if (Check(TokenKind::kKwProgram)) {
    unit->programs.push_back(ParseExternInterfaceOrProgramDecl());
    unit->programs.back()->attrs = std::move(attrs);
    return;
  }
  if (Check(TokenKind::kKwPrimitive)) {
    auto* udp = ParseExternUdpDecl();
    udp->attrs = std::move(attrs);
    unit->udps.push_back(udp);
    known_udps_.insert(udp->name);
    return;
  }
  if (Check(TokenKind::kKwTask) || Check(TokenKind::kKwFunction) ||
      Check(TokenKind::kKwForkjoin)) {
    ParseExternTfDeclaration(extern_loc);
    return;
  }
  diag_.Error(CurrentLoc(),
              "the token after 'extern' opens no module, interface, program or "
              "primitive header",
              Subclause("A.1.2"));
  SkipToSemicolon(lexer_);
}

ModuleDecl* Parser::ParseExternInterfaceOrProgramDecl() {
  TypeNameScope type_scope(*this);
  const bool kIsInterface = Check(TokenKind::kKwInterface);
  auto* decl = arena_.Create<ModuleDecl>();
  decl->decl_kind =
      kIsInterface ? ModuleDeclKind::kInterface : ModuleDeclKind::kProgram;
  decl->is_extern = true;
  decl->range.start = CurrentLoc();
  Consume();
  Match(TokenKind::kKwAutomatic) || Match(TokenKind::kKwStatic);
  decl->name =
      Expect(TokenKind::kIdentifier, Subclause(kIsInterface ? "25.3" : "24.3"))
          .text;
  declared_design_elements_.insert(decl->name);
  ParseParamsPortsAndSemicolon(*decl);
  return decl;
}

ModuleDecl* Parser::ParseExternModuleDecl() {
  TypeNameScope type_scope(*this);
  auto* mod = arena_.Create<ModuleDecl>();
  mod->is_extern = true;
  mod->range.start = CurrentLoc();
  if (!Match(TokenKind::kKwMacromodule)) {
    Expect(TokenKind::kKwModule, Subclause("23.5"));
  }
  mod->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!mod->is_automatic) Match(TokenKind::kKwStatic);
  mod->name = Expect(TokenKind::kIdentifier, Subclause("23.5")).text;
  declared_design_elements_.insert(mod->name);
  ParseParamsPortsAndSemicolon(*mod);
  mod->range.end = CurrentLoc();
  return mod;
}

ModuleDecl* Parser::ParseModuleDecl() {
  auto* mod = arena_.Create<ModuleDecl>();
  TypeNameScope type_scope(*this);
  auto loc = CurrentLoc();
  if (!Match(TokenKind::kKwMacromodule)) {
    Expect(TokenKind::kKwModule, Subclause("23.2.1"));
  }

  mod->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!mod->is_automatic) Match(TokenKind::kKwStatic);

  auto name_tok = ExpectIdentifier(Subclause("23.2.1"));
  mod->name = name_tok.text;
  mod->range.start = loc;
  declared_design_elements_.insert(mod->name);

  ParseParamsPortsAndSemicolon(*mod);
  ParseModuleBody(*mod);
  Expect(TokenKind::kKwEndmodule, Subclause("23.2"));
  MatchEndLabel(mod->name);
  mod->range.end = CurrentLoc();
  return mod;
}

bool Parser::TryParsePackageBodyItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwProgram)) {
    Consume();
    Expect(TokenKind::kSemicolon, Subclause("24.6"));
    bool prev_anon = in_anonymous_program_;
    in_anonymous_program_ = true;
    while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
      if (Match(TokenKind::kSemicolon)) continue;
      size_t before = items.size();
      ParseModuleItem(items);
      FilterAnonymousProgramItems(diag_, items, before);
    }
    in_anonymous_program_ = prev_anon;
    Expect(TokenKind::kKwEndprogram, Subclause("24.6"));
    return true;
  }

  return TryParseExternConstraintItem(items);
}

PackageDecl* Parser::ParsePackageDecl() {
  TypeNameScope type_scope(*this);
  auto* pkg = arena_.Create<PackageDecl>();
  pkg->range.start = CurrentLoc();
  Expect(TokenKind::kKwPackage, Subclause("26.2"));

  if (Match(TokenKind::kKwAutomatic)) {
    pkg->is_automatic = true;
  } else {
    Match(TokenKind::kKwStatic);
  }

  pkg->name = Expect(TokenKind::kIdentifier, Subclause("26.2")).text;
  Expect(TokenKind::kSemicolon, Subclause("26.2"));

  auto* prev_package = current_package_;
  current_package_ = pkg;
  ++package_body_depth_;
  while (!Check(TokenKind::kKwEndpackage) && !AtEnd()) {
    if (NoteItemAndMatchNull(pkg->has_read_body_item)) continue;

    if (Check(TokenKind::kKwSpecify)) {
      diag_.Error(CurrentLoc(),
                  "specify block must appear inside a module declaration",
                  Subclause("30.3"));
      ParseSpecifyBlock();
      continue;
    }
    if (!TryParsePackageBodyItem(pkg->items)) {
      size_t before = pkg->items.size();
      ParseModuleItem(pkg->items);
      FilterPackageItems(pkg->items, before);
    }
  }
  --package_body_depth_;
  current_package_ = prev_package;
  package_types_[pkg->name] = type_scope.NamesAddedSoFar();
  Expect(TokenKind::kKwEndpackage, Subclause("26.2"));
  MatchEndLabel(pkg->name);
  pkg->range.end = CurrentLoc();
  return pkg;
}

void Parser::ParseGenvarDecl(std::vector<ModuleItem*>& items) {
  Consume();
  do {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kVarDecl;
    item->is_genvar = true;
    item->loc = CurrentLoc();
    item->name = Expect(TokenKind::kIdentifier, Subclause("27.4")).text;
    items.push_back(item);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("27.4"));
}

}  // namespace delta
