#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_prototype_validate.h"
#include "parser/parser_token_skips.h"

namespace delta {

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
    refs.has_other_items = !mod->items.empty() || mod->has_read_body_item;
  } else if (validate_pkg) {
    refs.active = true;
    refs.has_unit = &pkg->has_timeunit;
    refs.has_prec = &pkg->has_timeprecision;
    refs.unit = &pkg->time_unit;
    refs.prec = &pkg->time_prec;
    refs.unit_mag = &pkg->time_unit_magnitude;
    refs.prec_mag = &pkg->time_prec_magnitude;
    refs.has_other_items = !pkg->items.empty() || pkg->has_read_body_item;
  }
  refs.was_unit_set = refs.has_unit && *refs.has_unit;
  refs.was_prec_set = refs.has_prec && *refs.has_prec;
  refs.old_unit = refs.was_unit_set ? *refs.unit : TimeUnit{};
  refs.old_unit_mag = refs.was_unit_set ? *refs.unit_mag : 0;
  refs.old_prec = refs.was_prec_set ? *refs.prec : TimeUnit{};
  refs.old_prec_mag = refs.was_prec_set ? *refs.prec_mag : 0;
  return refs;
}

void ValidateTimeScopeAfterParse(const TimeScopeRefs& refs, DiagEngine& diag,
                                 SourceLoc loc) {
  if (!refs.active) return;
  if (*refs.has_unit && !refs.was_unit_set && refs.has_other_items)
    diag.Error(loc,
               "timeunit as a later item requires a matching prior "
               "declaration in the same time scope",
               Subclause("3.14.2.2"));
  else if (refs.was_unit_set &&
           (*refs.unit != refs.old_unit || *refs.unit_mag != refs.old_unit_mag))
    diag.Error(loc, "timeunit does not match prior declaration",
               Subclause("3.14.2.2"));
  if (*refs.has_prec && !refs.was_prec_set && refs.has_other_items)
    diag.Error(loc,
               "timeprecision as a later item requires a matching prior "
               "declaration in the same time scope",
               Subclause("3.14.2.2"));
  else if (refs.was_prec_set &&
           (*refs.prec != refs.old_prec || *refs.prec_mag != refs.old_prec_mag))
    diag.Error(loc, "timeprecision does not match prior declaration",
               Subclause("3.14.2.2"));
}

DataType MakeInterconnectDataType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kWire;
  dtype.is_net = true;
  dtype.is_interconnect = true;
  return dtype;
}

DataType MakeScopedNamedType(std::string_view scope_name,
                             std::string_view type_name) {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.scope_name = scope_name;
  dtype.type_name = type_name;
  return dtype;
}

DataType MakeNamedType(std::string_view type_name) {
  DataType dtype;
  dtype.kind = DataTypeKind::kNamed;
  dtype.type_name = type_name;
  return dtype;
}

void StampInstScope(std::vector<ModuleItem*>& items, size_t start,
                    std::string_view scope_name) {
  for (size_t i = start; i < items.size(); ++i)
    items[i]->inst_scope = scope_name;
}

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
  if (TryParseSpecifyItem(items)) return true;
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
      Expect(TokenKind::kKwIff, Subclause("16.15"));
      auto* item = arena_.Create<ModuleItem>();
      item->kind = ModuleItemKind::kDefaultDisableIff;
      item->loc = CurrentLoc();
      item->init_expr = ParseExpr();
      Expect(TokenKind::kSemicolon, Subclause("16.15"));
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
      diag_.Error(CurrentLoc(), "always procedures not allowed in programs",
                  Subclause("24.3"));
    items.push_back(ParseAlwaysBlock(*ak));
    return true;
  }
  return false;
}

bool Parser::AtMisplacedMethodQualifier() {
  if (!Check(TokenKind::kKwPure) && !Check(TokenKind::kKwVirtual)) return false;
  auto saved = lexer_.SavePos();
  Match(TokenKind::kKwPure);
  bool on_subroutine =
      Match(TokenKind::kKwVirtual) &&
      (Check(TokenKind::kKwTask) || Check(TokenKind::kKwFunction));
  lexer_.RestorePos(saved);
  return on_subroutine;
}

void Parser::RejectMisplacedMethodQualifier(std::vector<ModuleItem*>& items) {
  SourceLoc loc = CurrentLoc();
  bool is_prototype = Match(TokenKind::kKwPure);
  Match(TokenKind::kKwVirtual);
  bool is_task = Check(TokenKind::kKwTask);
  diag_.Error(loc,
              "'virtual' is a class method qualifier, so it may appear only on "
              "a method declared inside a class",
              is_task ? Subclause("13.3") : Subclause("13.4"));
  items.push_back(is_task ? ParseTaskDecl(is_prototype)
                          : ParseFunctionDecl(is_prototype));
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
  if (AtMisplacedMethodQualifier()) {
    RejectMisplacedMethodQualifier(items);
    return true;
  }
  if (Check(TokenKind::kKwFunction)) {
    items.push_back(ParseFunctionDecl());
    return true;
  }
  if (Check(TokenKind::kKwTask)) {
    RejectInCheckerBody(
        "a task declaration is not an item of a checker; a checker's "
        "subroutine is a function");
    items.push_back(ParseTaskDecl());
    return true;
  }
  if (Check(TokenKind::kKwExtern)) {
    SourceLoc extern_loc = CurrentLoc();
    Consume();
    if (ModuleDecl* decl = TryParseNestedExternDecl(extern_loc)) {
      auto* item = arena_.Create<ModuleItem>();
      item->kind = ModuleItemKind::kNestedModuleDecl;
      item->loc = decl->range.start;
      item->nested_module_decl = decl;
      items.push_back(item);
      return true;
    }
    items.push_back(ParseExternTfDeclaration(extern_loc));
    return true;
  }
  return false;
}

ModuleItem* Parser::ParseExternTfDeclaration(SourceLoc extern_loc) {
  if (!InInterfaceBody() && !in_anonymous_program_) {
    diag_.Error(extern_loc,
                "an extern task or function prototype is an item of an "
                "interface",
                Subclause("A.1.6"));
  }
  bool forkjoin = Match(TokenKind::kKwForkjoin);
  ModuleItem* item = nullptr;
  if (forkjoin || Check(TokenKind::kKwTask)) {
    item = ParseTaskDecl(true);
  } else {
    item = ParseFunctionDecl(true);
  }
  item->is_extern = true;
  item->is_forkjoin = forkjoin;
  ValidateExternTfPrototype(diag_, item);
  return item;
}

void Parser::ParseTimeunitItem() {
  if (InGenerateBlock() || in_generate_region_) {
    diag_.Error(CurrentLoc(),
                "a timeunit or timeprecision declaration is not an item of a "
                "generate block or region, which is no time scope",
                Subclause("3.14.2.2"));
    ParseTimeunitDecl(nullptr, nullptr, nullptr);
    return;
  }
  bool validate_pkg = !current_module_ && current_package_ != nullptr;
  TimeScopeRefs refs = CollectTimeScopeRefs(current_module_, current_package_);
  auto loc = CurrentLoc();
  ParseTimeunitDecl(current_module_, nullptr,
                    validate_pkg ? current_package_ : nullptr);
  ValidateTimeScopeAfterParse(refs, diag_, loc);
}

bool Parser::NoteItemAndMatchNull(bool& has_read_item) {
  if (!Check(TokenKind::kKwTimeunit) && !Check(TokenKind::kKwTimeprecision)) {
    has_read_item = true;
  }
  return Match(TokenKind::kSemicolon);
}

void Parser::ParseInterconnectItem(std::vector<ModuleItem*>& items) {
  Consume();
  DataType dtype = MakeInterconnectDataType();
  dtype.is_signed = Match(TokenKind::kKwSigned);
  if (!dtype.is_signed) Match(TokenKind::kKwUnsigned);
  ParsePackedDims(dtype);
  if (Check(TokenKind::kHash)) {
    auto saved = lexer_.SavePos();
    auto loc = CurrentLoc();
    Consume();
    bool parenthesized = Check(TokenKind::kLParen);
    lexer_.RestorePos(saved);
    if (parenthesized) {
      diag_.Error(loc,
                  "an interconnect net's delay is one delay value written "
                  "without parentheses",
                  Subclause("10.3"));
    }
  }
  const size_t kFirst = items.size();
  ParseVarDeclList(items, dtype);
  for (size_t i = kFirst + 2; i < items.size(); ++i) {
    diag_.Error(items[i]->loc,
                "an interconnect declaration names one net, or two",
                Subclause("A.2.1.3"));
  }
}

void Parser::RejectProceduralContinuousAssignItem() {
  const Token& kw = CurrentToken();
  diag_.Error(kw.loc,
              std::string("'") + std::string(kw.text) +
                  "' is a procedural continuous assignment statement and is "
                  "placed within a procedure; outside any procedure the "
                  "assignment is the continuous 'assign' alone",
              Subclause("C.4.2"));
  SkipToSemicolon(lexer_);
}

bool Parser::TryParseMiscKeywordItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwAssign)) {
    ParseContinuousAssign(items);
    return true;
  }
  if (Check(TokenKind::kKwDeassign) || Check(TokenKind::kKwForce) ||
      Check(TokenKind::kKwRelease)) {
    RejectProceduralContinuousAssignItem();
    return true;
  }
  if (TryParseProcessBlock(items)) return true;
  if (Check(TokenKind::kKwAlias)) {
    RejectInCheckerBody("a net alias is not an item of a checker");
    RejectInProgramBody(CurrentLoc(),
                        "a net alias is not an item of a program");
    items.push_back(ParseAlias());
    return true;
  }
  if (Check(TokenKind::kKwGenvar)) {
    ParseGenvarDecl(items);
    return true;
  }
  if (IsTimeunitKeyword(CurrentToken().kind)) {
    RejectInCheckerBody(
        "a timeunit or timeprecision declaration is not an item of a "
        "checker; a checker sets no time scope");
    ParseTimeunitItem();
    return true;
  }
  if (Check(TokenKind::kKwLet)) {
    items.push_back(ParseLetDecl());
    return true;
  }
  if (Check(TokenKind::kKwInterconnect)) {
    ParseInterconnectItem(items);
    return true;
  }
  if (Check(TokenKind::kKwBind)) {
    ParseBindItem(items);
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
    RejectInCheckerBody("a class declaration is not an item of a checker");
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
                  "interface declarations not allowed in programs",
                  Subclause("24.3"));
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
    Expect(TokenKind::kSemicolon, Subclause("20.10.1"));
    items.push_back(item);
    return true;
  }
  if (Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule)) {
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "module declarations not allowed in programs",
                  Subclause("24.3"));
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kNestedModuleDecl;
    item->loc = CurrentLoc();
    item->nested_module_decl = ParseModuleDecl();
    items.push_back(item);
    return true;
  }
  if (Check(TokenKind::kKwProgram)) {
    if (InProgramBlock())
      diag_.Error(CurrentLoc(), "program declarations not allowed in programs",
                  Subclause("24.3"));
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
  if (!Check(TokenKind::kKwAssert) && !Check(TokenKind::kKwAssume) &&
      !Check(TokenKind::kKwCover) && !Check(TokenKind::kKwRestrict)) {
    lexer_.RestorePos(saved);
    return {};
  }
  return label_tok.text;
}

void Parser::ParseModuleItem(std::vector<ModuleItem*>& items) {
  const SourceLoc kAttrLoc = CurrentLoc();
  auto attrs = ParseAttributes();
  if (!attrs.empty()) RejectAttributesBeforeItem(kAttrLoc);
  size_t before = items.size();

  auto assertion_label = TryParseAssertionItemLabel();

  if (TryRejectBodyPortDecl()) return;

  if (TryParseExternConstraintItem(items)) {
    return;
  }
  if (TryParseKeywordItem(items)) {
    ApplyAssertionLabel(items, before, assertion_label);
  } else if (Check(TokenKind::kKwParameter) ||
             Check(TokenKind::kKwLocalparam)) {
    RejectInCheckerBody(
        "a parameter declaration is not an item of a checker; a checker "
        "takes an elaboration-time constant through a formal argument");
    ParseParamDecl(items);
  } else if (Check(TokenKind::kKwDefparam)) {
    RejectInCheckerBody("a defparam statement is not an item of a checker");
    RejectInProgramBody(CurrentLoc(),
                        "a defparam statement is not an item of a program");
    RejectInInterfaceBody(
        "a defparam statement is not an item of an interface");
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

bool Parser::LooksLikeScopedInstTail() {
  auto saved = lexer_.SavePos();
  if (Check(TokenKind::kHash)) {
    Consume();
    SkipBalancedParens();
  }
  bool has_name = CheckIdentifier();
  if (has_name) {
    Consume();
    SkipBracketedDims();
  }
  bool is_inst = has_name && Check(TokenKind::kLParen);
  lexer_.RestorePos(saved);
  return is_inst;
}

void Parser::ParseScopedTypeOrInst(const Token& name_tok,
                                   std::vector<ModuleItem*>& items) {
  Consume();
  auto type_tok = ExpectIdentifier(Subclause("23.7.1"));
  bool is_builtin_pkg = name_tok.text == "std";
  bool is_scoped_inst = !is_builtin_pkg && LooksLikeScopedInstTail();
  if (is_scoped_inst) {
    auto start = items.size();
    ParseModuleInstList(type_tok, &items);
    StampInstScope(items, start, name_tok.text);
    return;
  }
  DataType dtype = MakeScopedNamedType(name_tok.text, type_tok.text);
  bool assignment_written = Check(TokenKind::kHash);
  if (assignment_written) {
    Consume();
    dtype.type_params = ParseTypeParamList();
  }
  while (Check(TokenKind::kColonColon)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (!CheckIdentifier()) {
      lexer_.RestorePos(saved);
      break;
    }
    dtype.outer_scope_names.push_back(dtype.scope_name);
    dtype.scope_name = dtype.type_name;
    dtype.scope_param_assignment_written = assignment_written;
    dtype.type_name = Consume().text;
    assignment_written = Check(TokenKind::kHash);
    if (assignment_written) {
      Consume();
      dtype.type_params = ParseTypeParamList();
    }
  }
  ParsePackedDims(dtype);
  ParseVarDeclList(items, dtype);
}

void Parser::ParsePlainVarDecl(const Token& name_tok,
                               std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kVarDecl;
  item->loc = name_tok.loc;
  item->name = name_tok.text;
  if (Match(TokenKind::kEq)) item->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("6.8"));
  items.push_back(item);
}

bool Parser::LooksLikeUndeclaredTypeDecl() {
  return CheckIdentifier() && !LooksLikeScopedInstTail();
}

void Parser::ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items) {
  auto name_tok = Consume();

  if (Check(TokenKind::kColonColon)) {
    ParseScopedTypeOrInst(name_tok, items);
    return;
  }
  if (known_types_.count(name_tok.text) != 0) {
    DataType dtype = MakeNamedType(name_tok.text);
    if (Check(TokenKind::kHash) && known_nettypes_.count(name_tok.text) == 0) {
      Consume();
      dtype.type_params = ParseTypeParamList();
    }
    ParseVarDeclList(items, dtype);
    return;
  }
  if (known_udps_.count(name_tok.text) != 0 || AtUdpOnlyInstanceForm()) {
    if (InProgramBlock()) {
      diag_.Error(name_tok.loc, "primitive instances not allowed in programs",
                  Subclause("24.3"));
    }
    ParseUdpInstList(name_tok, items);
    return;
  }
  if (LooksLikeUndeclaredTypeDecl()) {
    auto start = items.size();
    ParseVarDeclList(items, MakeNamedType(name_tok.text));
    for (auto i = start; i < items.size(); ++i) {
      items[i]->type_name_undeclared_at_parse = true;
    }
    return;
  }
  if (CheckIdentifier() || Check(TokenKind::kHash)) {
    RejectInstInProgram(name_tok.loc, name_tok.text,
                        "instantiations not allowed in programs");
    ParseModuleInstList(name_tok, &items);
    return;
  }
  ParsePlainVarDecl(name_tok, items);
}

}  // namespace delta
