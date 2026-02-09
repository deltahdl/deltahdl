#include "parser/parser.h"

namespace delta {

// Parse: config name; ... endconfig [: name]
// Skip config body contents (design, default, instance, cell, liblist, use).
ConfigDecl* Parser::ParseConfigDecl() {
  auto* decl = arena_.Create<ConfigDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwConfig);
  decl->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);

  // Skip body until endconfig
  while (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndconfig);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
