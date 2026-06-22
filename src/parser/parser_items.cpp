#include <optional>

#include "parser/parser.h"
#include "parser/time_resolve.h"

namespace delta {

static bool IsElabSeverityTask(TokenKind kind, std::string_view text) {
  return kind == TokenKind::kSystemIdentifier &&
         (text == "$fatal" || text == "$error" || text == "$warning" ||
          text == "$info");
}

// True for the two keywords that head a §3.14.2 time-scope declaration.
// Factored out so the misc-keyword dispatcher tests one predicate instead of an
// inline disjunction.
static bool IsTimeunitKeyword(TokenKind kind) {
  return kind == TokenKind::kKwTimeunit || kind == TokenKind::kKwTimeprecision;
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

namespace {

// Mutable pointers into the time-scope fields of the module or package that
// owns the timeunit/timeprecision declaration currently being parsed, plus a
// snapshot of the prior state captured before parsing so the post-parse
// validation can detect mismatches.
struct TimeScopeRefs {
  bool active = false;
  bool* has_unit = nullptr;
  bool* has_prec = nullptr;
  TimeUnit* unit = nullptr;
  TimeUnit* prec = nullptr;
  int* unit_mag = nullptr;
  int* prec_mag = nullptr;
  bool has_other_items = false;
  bool was_unit_set = false;
  bool was_prec_set = false;
  TimeUnit old_unit{};
  int old_unit_mag = 0;
  TimeUnit old_prec{};
  int old_prec_mag = 0;
};

// Binds the time-scope pointers to whichever of the module/package owns the
// declaration and snapshots the prior values for later mismatch checks.
TimeScopeRefs CollectTimeScopeRefs(ModuleDecl* mod, PackageDecl* pkg) {
  TimeScopeRefs refs;
  bool validate_mod = mod && (mod->decl_kind == ModuleDeclKind::kModule ||
                              mod->decl_kind == ModuleDeclKind::kInterface ||
                              mod->decl_kind == ModuleDeclKind::kProgram);
  bool validate_pkg = !mod && pkg != nullptr;
  if (validate_mod) {
    refs.active = true;
    refs.has_unit = &mod->has_timeunit;
    refs.has_prec = &mod->has_timeprecision;
    refs.unit = &mod->time_unit;
    refs.prec = &mod->time_prec;
    refs.unit_mag = &mod->time_unit_magnitude;
    refs.prec_mag = &mod->time_prec_magnitude;
    refs.has_other_items = !mod->items.empty();
  } else if (validate_pkg) {
    refs.active = true;
    refs.has_unit = &pkg->has_timeunit;
    refs.has_prec = &pkg->has_timeprecision;
    refs.unit = &pkg->time_unit;
    refs.prec = &pkg->time_prec;
    refs.unit_mag = &pkg->time_unit_magnitude;
    refs.prec_mag = &pkg->time_prec_magnitude;
    refs.has_other_items = !pkg->items.empty();
  }
  refs.was_unit_set = refs.has_unit && *refs.has_unit;
  refs.was_prec_set = refs.has_prec && *refs.has_prec;
  refs.old_unit = refs.was_unit_set ? *refs.unit : TimeUnit{};
  refs.old_unit_mag = refs.was_unit_set ? *refs.unit_mag : 0;
  refs.old_prec = refs.was_prec_set ? *refs.prec : TimeUnit{};
  refs.old_prec_mag = refs.was_prec_set ? *refs.prec_mag : 0;
  return refs;
}

// Emits the §3.14.2 diagnostics comparing the just-parsed timeunit/
// timeprecision against the snapshot captured in CollectTimeScopeRefs.
void ValidateTimeScopeAfterParse(const TimeScopeRefs& refs, DiagEngine& diag,
                                 SourceLoc loc) {
  if (!refs.active) return;
  if (*refs.has_unit && !refs.was_unit_set && refs.has_other_items)
    diag.Error(loc,
               "timeunit as a later item requires a matching prior "
               "declaration in the same time scope");
  else if (refs.was_unit_set &&
           (*refs.unit != refs.old_unit || *refs.unit_mag != refs.old_unit_mag))
    diag.Error(loc, "timeunit does not match prior declaration");
  if (*refs.has_prec && !refs.was_prec_set && refs.has_other_items)
    diag.Error(loc,
               "timeprecision as a later item requires a matching prior "
               "declaration in the same time scope");
  else if (refs.was_prec_set &&
           (*refs.prec != refs.old_prec || *refs.prec_mag != refs.old_prec_mag))
    diag.Error(loc, "timeprecision does not match prior declaration");
}

// Builds the fixed (keyword-independent) part of an `interconnect` net's
// data type; the optional signedness is filled in by the caller.
DataType MakeInterconnectDataType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kWire;
  dtype.is_net = true;
  dtype.is_interconnect = true;
  return dtype;
}

// Builds a named data type carrying an optional package/class scope name.
// The caller fills in any parameterized type arguments after the `#`.
DataType MakeScopedNamedType(std::string_view scope_name,
                             std::string_view type_name) {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.scope_name = scope_name;
  dtype.type_name = type_name;
  return dtype;
}

// Builds an unscoped named (type_identifier) data type.
DataType MakeNamedType(std::string_view type_name) {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = type_name;
  return dtype;
}

// Stamps the resolved package/class scope name onto each instantiation item
// produced for a `scope :: module #(...) inst(...)` form.
void StampInstScope(std::vector<ModuleItem*>& items, size_t start,
                    std::string_view scope_name) {
  for (size_t i = start; i < items.size(); ++i)
    items[i]->inst_scope = scope_name;
}

// Propagates a deferred-immediate / concurrent assertion item's optional
// block_identifier label onto each item produced for it (§16.14), filling the
// item name and its statement body label only where still unset.
void ApplyAssertionLabel(std::vector<ModuleItem*>& items, size_t before,
                         std::string_view label) {
  if (label.empty()) return;
  for (size_t i = before; i < items.size(); ++i) {
    if (items[i]->name.empty()) items[i]->name = label;
    if (items[i]->body && items[i]->body->label.empty()) {
      items[i]->body->label = label;
    }
  }
}

}  // namespace

bool Parser::TryParseClockingOrVerification(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwSpecify)) {
    if (InGenerateBlock()) {
      diag_.Error(CurrentLoc(),
                  "specify block not allowed inside a generate block");
    }
    items.push_back(ParseSpecifyBlock());
    return true;
  }
  if (Check(TokenKind::kKwSpecparam)) {
    if (InGenerateBlock()) {
      diag_.Error(CurrentLoc(),
                  "specparam declaration not allowed inside a generate block");
    }
    ParseSpecparamDecl(items);
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
      Consume();
      Consume();
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
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "always procedures not allowed in programs");
    items.push_back(ParseAlwaysBlock(*ak));
    return true;
  }
  return false;
}

bool Parser::IsAtClassDecl() {
  if (Check(TokenKind::kKwClass)) return true;
  if (!Check(TokenKind::kKwVirtual) && !Check(TokenKind::kKwInterface)) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();
  bool result = Check(TokenKind::kKwClass);
  lexer_.RestorePos(saved);
  return result;
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
  if (Check(TokenKind::kKwExtern)) {
    Consume();
    bool forkjoin = Match(TokenKind::kKwForkjoin);
    ModuleItem* item = nullptr;
    if (forkjoin || Check(TokenKind::kKwTask)) {
      item = ParseTaskDecl(true);
    } else {
      item = ParseFunctionDecl(true);
    }
    item->is_extern = true;
    item->is_forkjoin = forkjoin;
    items.push_back(item);
    return true;
  }
  return false;
}

bool Parser::TryParseMiscKeywordItem(std::vector<ModuleItem*>& items) {
  // Parses a timeunit/timeprecision declaration with its surrounding §3.14.2
  // snapshot/validate dance. Kept as a local lambda so its branch logic is
  // scored separately and does not inflate this dispatcher's complexity.
  auto parse_timeunit = [&] {
    bool validate_pkg = !current_module_ && current_package_ != nullptr;
    TimeScopeRefs refs =
        CollectTimeScopeRefs(current_module_, current_package_);
    auto loc = CurrentLoc();
    ParseTimeunitDecl(current_module_, nullptr,
                      validate_pkg ? current_package_ : nullptr);
    ValidateTimeScopeAfterParse(refs, diag_, loc);
  };
  // Parses an `interconnect` net declaration (§6.6.8), including its optional
  // signedness and packed dimensions, into a var-decl list.
  auto parse_interconnect = [&] {
    Consume();
    DataType dtype = MakeInterconnectDataType();
    dtype.is_signed = Match(TokenKind::kKwSigned);
    if (!dtype.is_signed) Match(TokenKind::kKwUnsigned);
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
  };

  if (Check(TokenKind::kKwAssign)) {
    ParseContinuousAssign(items);
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
  if (IsTimeunitKeyword(CurrentToken().kind)) {
    parse_timeunit();
    return true;
  }
  if (Check(TokenKind::kKwLet)) {
    items.push_back(ParseLetDecl());
    return true;
  }
  if (Check(TokenKind::kKwInterconnect)) {
    parse_interconnect();
    return true;
  }
  if (Check(TokenKind::kKwBind)) {
    auto* bd = ParseBindDirective();
    if (current_module_) current_module_->bind_directives.push_back(bd);
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
  if (Check(TokenKind::kKwInterface)) {
    if (InProgramBlock())
      diag_.Error(CurrentLoc(),
                  "interface declarations not allowed in programs");
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
  if (Check(TokenKind::kKwRestrict)) {
    items.push_back(ParseRestrictProperty());
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
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "module declarations not allowed in programs");
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseModuleDecl();
    items.push_back(item);
    return true;
  }
  if (Check(TokenKind::kKwProgram)) {
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "program declarations not allowed in programs");
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseProgramDecl();
    items.push_back(item);
    return true;
  }
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

std::string_view Parser::TryParseAssertionItemLabel() {
  if (!CheckIdentifier()) return {};
  auto saved = lexer_.SavePos();
  auto label_tok = Consume();
  if (!Match(TokenKind::kColon)) {
    lexer_.RestorePos(saved);
    return {};
  }
  // §16.14 Syntax 16-18: every concurrent_assertion_statement alternative —
  // assert, assume, cover, and restrict — may head a concurrent_assertion_item
  // and so carry the optional block_identifier name described in §16.14.
  if (!Check(TokenKind::kKwAssert) && !Check(TokenKind::kKwAssume) &&
      !Check(TokenKind::kKwCover) && !Check(TokenKind::kKwRestrict)) {
    lexer_.RestorePos(saved);
    return {};
  }
  return label_tok.text;
}

void Parser::ParseModuleItem(std::vector<ModuleItem*>& items) {
  auto attrs = ParseAttributes();
  size_t before = items.size();

  // §A.6.10 deferred_immediate_assertion_item permits an optional
  // [ block_identifier : ] label, mirroring concurrent_assertion_item.
  // Consume the label here so the dispatch below sees the bare keyword.
  auto assertion_label = TryParseAssertionItemLabel();

  // §27.2: a generate block may not contain port declarations. Top-level
  // non-ANSI port declarations are consumed directly in ParseModuleBody, so a
  // leading port direction reaching a generate-block item is always an illegal
  // non-ANSI port declaration. Reject it explicitly and recover past the
  // declaration, mirroring the specify/specparam rejections above.
  if (InGenerateBlock() && IsPortDirection(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "port declaration not allowed inside a generate block");
    while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEnd) &&
           !AtEnd()) {
      Consume();
    }
    Match(TokenKind::kSemicolon);
    return;
  }

  // Each branch parses one module_or_generate_item form; the shared
  // AttachAttrs is applied once after the dispatch. The data-declaration
  // fallback attaches its own attributes, so it returns early.
  if (TryParseKeywordItem(items)) {
    ApplyAssertionLabel(items, before, assertion_label);
  } else if (Check(TokenKind::kKwParameter) ||
             Check(TokenKind::kKwLocalparam)) {
    ParseParamDecl(items);
  } else if (Check(TokenKind::kKwDefparam)) {
    items.push_back(ParseDefparam());
  } else if (Check(TokenKind::kKwImport)) {
    ParseImportDecl(items);
  } else if (Check(TokenKind::kKwExport)) {
    ParseExportDecl(items);
  } else if (Check(TokenKind::kKwGenerate)) {
    ParseGenerateRegion(items);
  } else if (Check(TokenKind::kKwFor)) {
    items.push_back(ParseGenerateFor());
  } else if (Check(TokenKind::kKwIf)) {
    items.push_back(ParseGenerateIf());
  } else if (!TryParseNonPortItem(items)) {
    ParseDataDeclItem(items, before, attrs);
    return;
  }
  AttachAttrs(items, before, attrs);
}

void Parser::ParseDataDeclItem(std::vector<ModuleItem*>& items, size_t before,
                               const std::vector<Attribute>& attrs) {
  SourceLoc lifetime_loc = CurrentLoc();
  bool is_automatic = Match(TokenKind::kKwAutomatic);
  if (is_automatic) {
    diag_.Error(lifetime_loc,
                "'automatic' is not allowed in a data_declaration outside "
                "a procedural context");
  }
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);
  bool is_rand = Match(TokenKind::kKwRand);

  ParseTypedItemOrInst(items, is_automatic || is_static);
  for (size_t i = before; i < items.size(); ++i) {
    if (is_rand) items[i]->is_rand = true;
    if (is_automatic) items[i]->is_automatic = true;
    if (is_static) items[i]->is_static = true;
  }
  AttachAttrs(items, before, attrs);
}

void Parser::ParseVarPrefixed(std::vector<ModuleItem*>& items) {
  if (TryParseTypeRef(items)) return;
  if (Check(TokenKind::kKwEnum)) {
    auto dtype = ParseEnumType();
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
    return;
  }
  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    auto dtype = ParseStructOrUnionType();
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
    return;
  }
  auto dtype = ParseDataType();
  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    ParsePackedDims(dtype);
  }
  ParseVarDeclList(items, dtype);
}

void Parser::ParseTypedItemOrInst(std::vector<ModuleItem*>& items,
                                  bool had_lifetime) {
  if (Match(TokenKind::kKwVar)) {
    ParseVarPrefixed(items);
    return;
  }

  if (Check(TokenKind::kKwType)) {
    diag_.Error(CurrentLoc(),
                "type_reference in a variable declaration must be preceded "
                "by the 'var' keyword");
    TryParseTypeRef(items);
    return;
  }
  if (Check(TokenKind::kKwCase)) {
    items.push_back(ParseGenerateCase());
    return;
  }
  if (IsAtGateKeyword()) {
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "primitive instances not allowed in programs");
    ParseGateInst(items);
    return;
  }
  if (Check(TokenKind::kKwEnum)) {
    auto dtype = ParseEnumType();
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
    return;
  }
  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    auto dtype = ParseStructOrUnionType();
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
    return;
  }
  auto dtype = ParseDataType();
  if (dtype.kind != DataTypeKind::kImplicit || dtype.packed_dim_left ||
      dtype.is_signed || dtype.is_const) {
    ParseVarDeclList(items, dtype);
    return;
  }

  if (had_lifetime) {
    diag_.Error(CurrentLoc(),
                "data_declaration without an explicit data type requires "
                "the 'var' keyword");
    Synchronize();
    return;
  }
  if (!CheckIdentifier()) {
    diag_.Error(CurrentLoc(), "unexpected token in module body");
    // A stray block-closing keyword (e.g. endpackage from a misplaced package)
    // would otherwise make the enclosing body loop spin; recover with progress.
    SynchronizeWithProgress();
    return;
  }
  ParseImplicitTypeOrInst(items);
}

// §1800 forbids instantiating modules/primitives inside a program. Emits the
// matching diagnostic so each dispatch branch stays flat instead of nesting its
// own in-program guard.
void Parser::RejectInstInProgram(SourceLoc loc, const char* msg) {
  if (InProgramBlock()) diag_.Error(loc, msg);
}

// Parses a `name :: type_identifier ...` form (the `::` is consumed here) as
// either a scoped module instantiation or a variable declaration of a
// package/class-scoped type.
void Parser::ParseScopedTypeOrInst(const Token& name_tok,
                                   std::vector<ModuleItem*>& items) {
  Consume();  // ::
  auto type_tok = ExpectIdentifier();
  // The built-in package name `std` is reserved (it cannot hold modules), so
  // `std :: type_identifier` is a built_in_data_type. A declarator that follows
  // is a variable declaration of that scoped type rather than a scoped module
  // instantiation.
  bool is_builtin_pkg = name_tok.text == "std";
  bool is_scoped_inst =
      !is_builtin_pkg && (CheckIdentifier() || Check(TokenKind::kHash));
  if (is_scoped_inst) {
    RejectInstInProgram(name_tok.loc, "instantiations not allowed in programs");
    auto start = items.size();
    ParseModuleInstList(type_tok, &items);
    StampInstScope(items, start, name_tok.text);
    return;
  }
  DataType dtype = MakeScopedNamedType(name_tok.text, type_tok.text);
  // Parses the trailing `# (...)` parameter assignments of a scoped named type
  // (e.g. `pkg :: t #(...)`) onto the data type, if present.
  if (Check(TokenKind::kHash)) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }
  ParseVarDeclList(items, dtype);
}

// Builds the fallback bare-identifier variable declaration with optional
// initializer when the name is neither a scope, known type, UDP, nor inst.
void Parser::ParsePlainVarDecl(const Token& name_tok,
                               std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = name_tok.loc;
  item->name = name_tok.text;
  if (Match(TokenKind::kEq)) item->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  items.push_back(item);
}

void Parser::ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items) {
  auto name_tok = Consume();

  if (Check(TokenKind::kColonColon)) {
    ParseScopedTypeOrInst(name_tok, items);
    return;
  }
  if (known_types_.count(name_tok.text) != 0) {
    ParseVarDeclList(items, MakeNamedType(name_tok.text));
    return;
  }
  if (known_udps_.count(name_tok.text) != 0) {
    RejectInstInProgram(name_tok.loc,
                        "primitive instances not allowed in programs");
    ParseUdpInstList(name_tok, items);
    return;
  }
  if (CheckIdentifier() || Check(TokenKind::kHash)) {
    RejectInstInProgram(name_tok.loc, "instantiations not allowed in programs");
    ParseModuleInstList(name_tok, &items);
    return;
  }
  ParsePlainVarDecl(name_tok, items);
}

}  // namespace delta
