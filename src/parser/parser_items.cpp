#include <optional>

#include "parser/parser.h"
#include "parser/time_resolve.h"

namespace delta {

static bool IsElabSeverityTask(TokenKind kind, std::string_view text) {
  return kind == TokenKind::kSystemIdentifier &&
         (text == "$fatal" || text == "$error" || text == "$warning" ||
          text == "$info");
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
    if (InProgramBlock())  // §3.4
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
  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    bool validate = current_module_ &&
                    current_module_->decl_kind == ModuleDeclKind::kModule;
    bool was_unit_set = validate && current_module_->has_timeunit;
    bool was_prec_set = validate && current_module_->has_timeprecision;
    TimeUnit old_unit = was_unit_set ? current_module_->time_unit : TimeUnit{};
    TimeUnit old_prec = was_prec_set ? current_module_->time_prec : TimeUnit{};
    auto loc = CurrentLoc();
    ParseTimeunitDecl(current_module_);
    if (validate) {
      if (current_module_->has_timeunit && !was_unit_set)
        diag_.Error(loc,
                    "timeunit as module item requires a matching prior "
                    "declaration in the same scope");
      else if (was_unit_set && current_module_->time_unit != old_unit)
        diag_.Error(loc, "timeunit does not match prior declaration");
      if (current_module_->has_timeprecision && !was_prec_set)
        diag_.Error(loc,
                    "timeprecision as module item requires a matching prior "
                    "declaration in the same scope");
      else if (was_prec_set && current_module_->time_prec != old_prec)
        diag_.Error(loc, "timeprecision does not match prior declaration");
    }
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
    if (Match(TokenKind::kKwSigned)) {
      dtype.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
    ParsePackedDims(dtype);
    ParseVarDeclList(items, dtype);
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
  bool is_automatic = Match(TokenKind::kKwAutomatic);
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);
  bool is_rand = Match(TokenKind::kKwRand);
  ParseTypedItemOrInst(items);
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

void Parser::ParseTypedItemOrInst(std::vector<ModuleItem*>& items) {
  if (Match(TokenKind::kKwVar)) {
    ParseVarPrefixed(items);
    return;
  }
  if (TryParseTypeRef(items)) return;
  if (Check(TokenKind::kKwCase)) {
    items.push_back(ParseGenerateCase());
    return;
  }
  if (IsAtGateKeyword()) {
    if (InProgramBlock())  // §3.4
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
    Consume();
    auto type_tok = ExpectIdentifier();
    if (CheckIdentifier() || Check(TokenKind::kHash)) {
      if (InProgramBlock())
        diag_.Error(name_tok.loc, "instantiations not allowed in programs");
      auto start = items.size();
      ParseModuleInstList(type_tok, &items);
      for (auto i = start; i < items.size(); ++i)
        items[i]->inst_scope = name_tok.text;
      return;
    }
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
  if (known_udps_.count(name_tok.text) != 0) {
    if (InProgramBlock())  // §3.4
      diag_.Error(name_tok.loc, "primitive instances not allowed in programs");
    ParseUdpInstList(name_tok, items);
    return;
  }
  if (CheckIdentifier() || Check(TokenKind::kHash)) {
    if (InProgramBlock())
      diag_.Error(name_tok.loc, "instantiations not allowed in programs");
    ParseModuleInstList(name_tok, &items);
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
