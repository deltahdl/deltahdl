#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

void Parser::RejectInCheckerBody(const char* msg) {
  if (!InCheckerBody()) return;
  diag_.Error(CurrentLoc(), msg, Subclause("A.1.8"));
}

void Parser::RejectInProgramBody(SourceLoc loc, const char* msg) {
  if (!InProgramBlock()) return;
  diag_.Error(loc, msg, Subclause("A.1.7"));
}

void Parser::RejectAttributesBeforeItem(SourceLoc attr_loc) {
  if (!InModuleBody() && !InInterfaceBody() && !InProgramBlock()) return;
  Token tok = CurrentToken();
  const char* item = nullptr;
  if (tok.kind == TokenKind::kKwGenerate) {
    item = "a generate region";
  } else if (tok.kind == TokenKind::kKwSpecify) {
    item = "a specify block";
  } else if (IsTimeunitKeyword(tok.kind)) {
    item = "a timeunits declaration";
  } else if (InProgramBlock() &&
             (tok.kind == TokenKind::kKwIf || tok.kind == TokenKind::kKwFor ||
              tok.kind == TokenKind::kKwCase ||
              IsElabSeverityTask(tok.kind, tok.text))) {
    item = "a generate construct or elaboration system task of a program";
  }
  if (item == nullptr) return;
  const char* subclause = "A.1.7";
  if (InModuleBody()) {
    subclause = "A.1.4";
  } else if (InInterfaceBody()) {
    subclause = "A.1.6";
  }
  diag_.Error(attr_loc, std::format("{} takes no attribute instance", item),
              Subclause(subclause));
}

bool Parser::InModuleBody() const {
  return current_module_ &&
         current_module_->decl_kind == ModuleDeclKind::kModule;
}

bool Parser::InProgramBlock() const {
  return current_module_ &&
         current_module_->decl_kind == ModuleDeclKind::kProgram;
}

bool Parser::InInterfaceBody() const {
  return current_module_ &&
         current_module_->decl_kind == ModuleDeclKind::kInterface;
}

bool Parser::InPackageBody() const {
  return current_package_ != nullptr && current_module_ == nullptr &&
         !in_anonymous_program_;
}

bool Parser::InCheckerBody() const {
  return current_module_ &&
         current_module_->decl_kind == ModuleDeclKind::kChecker;
}

void Parser::RejectInInterfaceBody(const char* msg) {
  if (!InInterfaceBody()) return;
  diag_.Error(CurrentLoc(), msg, Subclause("A.1.6"));
}

ModuleDecl* Parser::TryParseNestedExternDecl(SourceLoc extern_loc) {
  const bool kIsModule =
      Check(TokenKind::kKwModule) || Check(TokenKind::kKwMacromodule);
  const char* program_report = nullptr;
  if (kIsModule) {
    program_report = "module declarations not allowed in programs";
  } else if (Check(TokenKind::kKwInterface)) {
    program_report = "interface declarations not allowed in programs";
  } else if (Check(TokenKind::kKwProgram)) {
    program_report = "program declarations not allowed in programs";
  } else {
    return nullptr;
  }
  if (InProgramBlock()) {
    diag_.Error(extern_loc, program_report, Subclause("24.3"));
  }
  return kIsModule ? ParseExternModuleDecl()
                   : ParseExternInterfaceOrProgramDecl();
}

void Parser::RejectMisplacedGate() {
  if (InProgramBlock()) {
    diag_.Error(CurrentLoc(), "primitive instances not allowed in programs",
                Subclause("24.3"));
  }
  RejectInCheckerBody("a gate instantiation is not an item of a checker");
  RejectInInterfaceBody("a gate instantiation is not an item of an interface");
}

void Parser::RejectInPackageBody(const char* msg) {
  if (!InPackageBody()) return;
  diag_.Error(CurrentLoc(), msg, Subclause("A.1.11"));
}

static const char* PackageItemRejection(const ModuleItem& item) {
  switch (item.kind) {
    case ModuleItemKind::kContAssign:
      return "a continuous assignment is not an item of a package";
    case ModuleItemKind::kGenerateFor:
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
      return "a generate construct is not an item of a package";
    case ModuleItemKind::kModuleInst:
      return "an instantiation is not an item of a package";
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
      return "a primitive instantiation is not an item of a package";
    case ModuleItemKind::kDefparam:
      return "a defparam statement is not an item of a package";
    case ModuleItemKind::kAlias:
      return "a net alias is not an item of a package";
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
      return "an assertion statement is not an item of a package; a package "
             "holds property, sequence and let declarations";
    case ModuleItemKind::kElabSystemTask:
      return "an elaboration system task is not an item of a package";
    case ModuleItemKind::kDefaultDisableIff:
      return "a default disable iff declaration is not an item of a package";
    case ModuleItemKind::kNestedModuleDecl:
      return item.nested_module_decl->decl_kind == ModuleDeclKind::kChecker
                 ? nullptr
                 : "a module, interface or program declaration is not an "
                   "item of a package";
    case ModuleItemKind::kVarDecl:
      return item.is_genvar ? "a genvar declaration is not an item of a package"
                            : nullptr;
    default:
      return nullptr;
  }
}

void Parser::FilterPackageItems(std::vector<ModuleItem*>& items,
                                size_t before) {
  size_t kept = before;
  for (size_t i = before; i < items.size(); ++i) {
    ModuleItem* item = items[i];
    const char* rejection = PackageItemRejection(*item);
    if (rejection != nullptr) {
      diag_.Error(item->loc, rejection, Subclause("A.1.11"));
      continue;
    }
    items[kept++] = item;
  }
  items.resize(kept);
}

static Subclause GenerateItemRule(bool in_block) {
  return in_block ? Subclause("27.2") : Subclause("A.4.2");
}

bool Parser::TryRejectBodyPortDecl() {
  if (!IsPortDirection(CurrentToken().kind)) return false;
  if (InGenerateBlock() || in_generate_region_) {
    diag_.Error(CurrentLoc(),
                "port declaration not allowed inside a generate block or "
                "region",
                GenerateItemRule(InGenerateBlock()));
  } else if (InCheckerBody()) {
    diag_.Error(CurrentLoc(),
                "a port declaration is not an item of a checker; its formal "
                "arguments are declared in its port list",
                Subclause("A.1.8"));
  } else if (InPackageBody()) {
    diag_.Error(CurrentLoc(),
                "a port declaration is not an item of a package; a package "
                "has no ports",
                Subclause("A.1.11"));
  } else {
    return false;
  }
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEnd) &&
         !AtEnd()) {
    Consume();
  }
  Match(TokenKind::kSemicolon);
  return true;
}

bool Parser::TryParseSpecifyItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwSpecify)) {
    if (InGenerateBlock() || in_generate_region_) {
      diag_.Error(CurrentLoc(),
                  "specify block not allowed inside a generate block or region",
                  GenerateItemRule(InGenerateBlock()));
    } else if (!InModuleBody() && !in_anonymous_program_) {
      diag_.Error(CurrentLoc(),
                  "specify block must appear inside a module declaration",
                  Subclause("30.3"));
    }
    items.push_back(ParseSpecifyBlock());
    return true;
  }
  if (Check(TokenKind::kKwSpecparam)) {
    if (InGenerateBlock() || in_generate_region_) {
      diag_.Error(CurrentLoc(),
                  "specparam declaration not allowed inside a generate block "
                  "or region",
                  GenerateItemRule(InGenerateBlock()));
    } else if (!InModuleBody() && !in_anonymous_program_) {
      diag_.Error(CurrentLoc(),
                  "specparam declaration must appear inside a module or a "
                  "specify block",
                  Subclause("6.20.5"));
    }
    ParseSpecparamDecl(items);
    return true;
  }
  return false;
}

void Parser::RejectInstInProgram(SourceLoc loc, std::string_view cell,
                                 const char* msg) {
  if (!InProgramBlock() || declared_design_elements_.count(cell) == 0) return;
  diag_.Error(loc, msg, Subclause("24.3"));
}

bool Parser::TryParseExternConstraintItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwStatic)) {
    auto saved = lexer_.SavePos();
    Consume();
    bool is_constraint = Check(TokenKind::kKwConstraint);
    lexer_.RestorePos(saved);
    if (!is_constraint) return false;
  } else if (!Check(TokenKind::kKwConstraint)) {
    return false;
  }
  bool admitted = true;
  if (InCheckerBody()) {
    RejectInCheckerBody(
        "an external constraint block is not an item of a checker");
    admitted = false;
  } else if (in_anonymous_program_) {
    diag_.Error(CurrentLoc(), kAnonymousProgramItemsMessage,
                Subclause("A.1.11"));
    admitted = false;
  }
  ParseOutOfBlockConstraint(admitted ? current_compilation_unit_ : nullptr,
                            &items);
  return true;
}

}  // namespace delta
