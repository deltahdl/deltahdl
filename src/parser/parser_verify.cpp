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

// The port kind of A.1.3 a checker formal was written with that no
// property_formal_type reaches, as the report words it, or null where it was
// written with none. An interface port is told by the spellings that say so,
// the `interface` keyword or a modport after a name: a name followed by an
// identifier alone reads the same whether the name is an interface's or a
// type's not yet declared, and ParsePortDecl takes it for the first.
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

// A checker formal as it is written, before ResolvePortDefaults gives it the
// direction and type it inherits -- for an input of a data type, the implicit
// net a module's input port of that type would be. A.1.8's checker_port_item
// names its formal with an identifier alone, where A.1.3's
// ansi_port_declaration also admits `. port_identifier ( [ expression ] )`.
// §17.2 lets the direction written be input or output, checker_port_direction's
// two alternatives, and makes the legal types of a formal those §16.12 makes
// legal for a property formal, which A.1.8 writes as a property_formal_type: a
// data type or an implicit one, `sequence`, `untyped` or `property`. A net
// type, `var` and an interface port header are A.1.3's port kinds, which none
// of those reaches.
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

// A.1.8 ends a checker_port_item with `= property_actual_arg`, which an event
// expression, a sequence or a property can be as well as an expression, and
// §17.2 has a checker declare a formal's default as §16.8 has a sequence
// declare one. So the default is read as a sequence's or a property's formal's
// is, and as an expression where it reads as no actual argument, which
// §16.14.7's inferred-value functions are left to be.
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
  // §17.2 with §26.2: a checker a package declares is a scope of its own, so
  // what its body declares, a clocking block among them, is the checker's and
  // not the package's (§14.7).
  const int kOuterPackageDepth = std::exchange(package_body_depth_, 0);
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    // §17.2: no module, interface, program or package may be declared within a
    // checker. The first three are read as items and left to the elaborator,
    // which reports them with the rest of the body's rules; a package is no
    // item of any body, so it is reported here and read to its `endpackage`,
    // and the checker's own body resumes after it.
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
