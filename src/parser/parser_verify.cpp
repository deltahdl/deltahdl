#include <format>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

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
  while (!Check(TokenKind::kKwEndchecker) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    // §17.2: "modules, interfaces, programs, and packages shall not be
    // declared inside checkers". The first three are read as items and left
    // to the elaborator, which reports them with the rest of the body's
    // rules; a package is no item of any body, so it is reported here and
    // read to its `endpackage`, and the checker's own body resumes after it.
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
  current_module_ = prev_module;
  Expect(TokenKind::kKwEndchecker, Subclause("17.2"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
