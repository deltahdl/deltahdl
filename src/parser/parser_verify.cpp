#include <format>
#include <utility>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

static const char* CheckerFormalPortKind(const PortDecl& port) {
  if (port.data_type.is_net) return "as a net";
  if (port.has_explicit_var) return "with 'var'";
  const bool kInterfaceKeyword =
      port.is_interface_port && port.data_type.kind != DataTypeKind::kNamed;
  if (kInterfaceKeyword || !port.data_type.modport_name.empty()) {
    return "as an interface port";
  }
  return nullptr;
}

void Parser::DiagnoseCheckerFormalAsWritten(const PortDecl& port) {
  if (port.is_explicit_named) {
    diag_.Error(port.loc,
                std::format("checker formal '{}' is named by an identifier "
                            "alone; a checker_port_item has no '.name(...)' "
                            "form",
                            port.name),
                Subclause("A.1.8"));
  }
  if (port.direction == Direction::kInout ||
      port.direction == Direction::kRef) {
    diag_.Error(
        port.loc,
        std::format("checker formal '{}' is declared '{}'; a checker "
                    "formal's direction is input or output",
                    port.name,
                    port.direction == Direction::kRef ? "ref" : "inout"),
        Subclause("17.2"));
  }
  if (const char* kind = CheckerFormalPortKind(port)) {
    diag_.Error(port.loc,
                std::format("checker formal '{}' is declared {}; its type "
                            "shall be one a property formal can take",
                            port.name, kind),
                Subclause("17.2"));
  }
}

Expr* Parser::ParseCheckerFormalDefault() {
  Expr* actual = ParserPropertySpecHelpers::ParseFormalDefault(*this);
  return actual != nullptr ? actual : ParseExpr();
}

ModuleDecl* Parser::ParseCheckerDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  TypeNameScope type_scope(*this);
  decl->decl_kind = ModuleDeclKind::kChecker;
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwChecker, Subclause("17.2"));
  decl->name = Expect(TokenKind::kIdentifier, Subclause("17.2")).text;
  ParseParamsPortsAndSemicolon(*decl);

  auto* prev_module = current_module_;
  current_module_ = decl;
  const int kOuterPackageDepth = std::exchange(package_body_depth_, 0);
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (Check(TokenKind::kKwPackage)) {
      diag_.Error(CurrentLoc(),
                  std::format("a package cannot be declared inside checker "
                              "'{}'",
                              decl->name),
                  Subclause("17.2"));
      ParsePackageDecl();
      continue;
    }
    ParseModuleItem(decl->items);
  }
  package_body_depth_ = kOuterPackageDepth;
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndchecker, Subclause("17.2"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
