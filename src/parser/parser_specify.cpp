#include "parser/parser.h"

namespace delta {

// Parse: specify ... endspecify
// Skip specify block contents (path delays, timing checks) for now.
// We consume tokens between specify/endspecify balanced.
ModuleItem* Parser::ParseSpecifyBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecifyBlock;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecify);

  // Skip body until endspecify
  while (!Check(TokenKind::kKwEndspecify) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndspecify);
  return item;
}

// Parse: specparam [range] name = expr {, name = expr} ;
ModuleItem* Parser::ParseSpecparamDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecparam;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam);

  // Optional packed dimension [msb:lsb]
  if (Check(TokenKind::kLBracket)) {
    Consume();
    item->data_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    item->data_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  item->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kEq);
  item->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return item;
}

}  // namespace delta
