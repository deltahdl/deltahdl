#include "parser/parser.h"

namespace delta {

void Parser::ParseGenerateRegion(std::vector<ModuleItem*>& items) {
  Expect(TokenKind::kKwGenerate);
  while (!Check(TokenKind::kKwEndgenerate) && !AtEnd()) {
    ParseModuleItem(items);
  }
  Expect(TokenKind::kKwEndgenerate);
}

ModuleItem* Parser::ParseGenerateFor() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateFor;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFor);
  Expect(TokenKind::kLParen);
  item->gen_init = ParseAssignmentOrExprStmt();
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kSemicolon);
  item->gen_step = ParseAssignmentOrExprNoSemi();
  Expect(TokenKind::kRParen);

  Expect(TokenKind::kKwBegin);
  while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
    ParseModuleItem(item->gen_body);
  }
  Expect(TokenKind::kKwEnd);
  return item;
}

ModuleItem* Parser::ParseGenerateIf() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateIf;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwIf);
  Expect(TokenKind::kLParen);
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen);

  Expect(TokenKind::kKwBegin);
  while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
    ParseModuleItem(item->gen_body);
  }
  Expect(TokenKind::kKwEnd);

  if (Match(TokenKind::kKwElse)) {
    if (Check(TokenKind::kKwIf)) {
      item->gen_else = ParseGenerateIf();
    } else {
      auto* else_item = arena_.Create<ModuleItem>();
      else_item->kind = ModuleItemKind::kGenerateIf;
      else_item->loc = CurrentLoc();
      Expect(TokenKind::kKwBegin);
      while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
        ParseModuleItem(else_item->gen_body);
      }
      Expect(TokenKind::kKwEnd);
      item->gen_else = else_item;
    }
  }
  return item;
}

ModuleItem* Parser::ParseGenerateCase() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateCase;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCase);
  Expect(TokenKind::kLParen);
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen);

  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    GenerateCaseItem ci;
    if (Match(TokenKind::kKwDefault)) {
      ci.is_default = true;
      Match(TokenKind::kColon);
    } else {
      ci.patterns.push_back(ParseExpr());
      while (Match(TokenKind::kComma)) {
        ci.patterns.push_back(ParseExpr());
      }
      Expect(TokenKind::kColon);
    }
    if (Check(TokenKind::kKwBegin)) {
      Expect(TokenKind::kKwBegin);
      while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
        ParseModuleItem(ci.body);
      }
      Expect(TokenKind::kKwEnd);
    } else {
      ParseModuleItem(ci.body);
    }
    item->gen_case_items.push_back(std::move(ci));
  }
  Expect(TokenKind::kKwEndcase);
  return item;
}

}  // namespace delta
