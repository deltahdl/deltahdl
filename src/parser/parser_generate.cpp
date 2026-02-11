#include "parser/parser.h"

namespace delta {

void Parser::ParseGenerateBody(std::vector<ModuleItem*>& body) {
  if (Match(TokenKind::kKwBegin)) {
    if (Match(TokenKind::kColon)) Match(TokenKind::kIdentifier);
    while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
      ParseModuleItem(body);
    }
    Expect(TokenKind::kKwEnd);
    if (Match(TokenKind::kColon)) Match(TokenKind::kIdentifier);
  } else {
    ParseModuleItem(body);  // single generate item
  }
}

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
  Match(TokenKind::kKwGenvar);  // optional inline genvar (§27.4)
  item->gen_init = ParseAssignmentOrExprStmt();
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kSemicolon);
  item->gen_step = ParseAssignmentOrExprNoSemi();
  Expect(TokenKind::kRParen);
  ParseGenerateBody(item->gen_body);
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
  ParseGenerateBody(item->gen_body);
  if (!Match(TokenKind::kKwElse)) return item;
  if (Check(TokenKind::kKwIf)) {
    item->gen_else = ParseGenerateIf();
  } else {
    auto* else_item = arena_.Create<ModuleItem>();
    else_item->kind = ModuleItemKind::kGenerateIf;
    else_item->loc = CurrentLoc();
    ParseGenerateBody(else_item->gen_body);
    item->gen_else = else_item;
  }
  return item;
}

void Parser::ParseGenerateCaseLabel(GenerateCaseItem& ci) {
  if (Match(TokenKind::kKwDefault)) {
    ci.is_default = true;
    Match(TokenKind::kColon);
    return;
  }
  ci.patterns.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    ci.patterns.push_back(ParseExpr());
  }
  Expect(TokenKind::kColon);
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
    ParseGenerateCaseLabel(ci);
    ParseGenerateBody(ci.body);
    item->gen_case_items.push_back(std::move(ci));
  }
  Expect(TokenKind::kKwEndcase);
  return item;
}

}  // namespace delta
