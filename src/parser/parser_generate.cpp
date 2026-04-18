#include "parser/parser.h"

namespace delta {

void Parser::ParseGenerateBody(std::vector<ModuleItem*>& body,
                               std::string_view& out_label) {
  // RAII guard so §27.2 rules apply across all return paths.
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(generate_block_depth_);

  // generate_block_or_null: ';' produces an empty body (§A.4.2)
  if (Match(TokenKind::kSemicolon)) return;

  // §9.3.5: label before generate begin-end block (identifier ':' 'begin')
  bool has_gen_label = false;
  if (CheckIdentifier()) {
    auto saved = lexer_.SavePos();
    auto ident = Consume();
    if (Check(TokenKind::kColon)) {
      Consume();
      if (Check(TokenKind::kKwBegin)) {
        has_gen_label = true;
        // §27.6: capture the prefix label so elaboration can use it as the
        // block's external name instead of assigning a default genblk<n>.
        out_label = ident.text;
      } else {
        lexer_.RestorePos(saved);
      }
    } else {
      lexer_.RestorePos(saved);
    }
  }

  if (Match(TokenKind::kKwBegin)) {
    if (!has_gen_label && Match(TokenKind::kColon)) {
      // §27.6: the alternative `begin : name` form also names the block.
      if (CheckIdentifier()) {
        out_label = Consume().text;
      }
    }
    if (has_gen_label && Check(TokenKind::kColon)) {
      diag_.Error(CurrentLoc(),
                  "cannot have both a generate block label and a block name");
    }
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
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwGenerate);
  // §27.3: generate regions shall not nest.
  if (in_generate_region_) {
    diag_.Error(loc, "generate regions shall not nest");
  }
  bool saved = in_generate_region_;
  in_generate_region_ = true;
  while (!Check(TokenKind::kKwEndgenerate) && !AtEnd()) {
    ParseModuleItem(items);
  }
  in_generate_region_ = saved;
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
  ParseGenerateBody(item->gen_body, item->name);
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
  ParseGenerateBody(item->gen_body, item->name);
  if (!Match(TokenKind::kKwElse)) return item;
  if (Check(TokenKind::kKwIf)) {
    item->gen_else = ParseGenerateIf();
  } else {
    auto* else_item = arena_.Create<ModuleItem>();
    else_item->kind = ModuleItemKind::kGenerateIf;
    else_item->loc = CurrentLoc();
    ParseGenerateBody(else_item->gen_body, else_item->name);
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
    ParseGenerateBody(ci.body, ci.label);
    item->gen_case_items.push_back(std::move(ci));
  }
  Expect(TokenKind::kKwEndcase);
  return item;
}

}  // namespace delta
