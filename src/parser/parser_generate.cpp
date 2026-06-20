#include "parser/parser.h"

namespace delta {

void Parser::ParseGenerateBody(std::vector<ModuleItem*>& body,
                               std::string_view& out_label) {
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(generate_block_depth_);

  if (Match(TokenKind::kSemicolon)) return;

  // Detect an optional `label :` prefix that introduces a named generate
  // block. Only commit to it when it is immediately followed by `begin`;
  // otherwise restore the lexer so the tokens are reparsed as an item.
  auto detect_gen_label = [&]() -> bool {
    if (!CheckIdentifier()) return false;
    auto saved = lexer_.SavePos();
    auto ident = Consume();
    bool committed = Check(TokenKind::kColon);
    if (committed) {
      Consume();
      committed = Check(TokenKind::kKwBegin);
    }
    if (!committed) {
      lexer_.RestorePos(saved);
      return false;
    }
    out_label = ident.text;
    return true;
  };
  bool has_gen_label = detect_gen_label();

  // Consume the optional `: name` block name at the head of a `begin` block,
  // diagnosing a conflict with a generate-block label.
  auto consume_begin_name = [&]() {
    if (!has_gen_label && Match(TokenKind::kColon)) {
      if (CheckIdentifier()) out_label = Consume().text;
      return;
    }
    if (has_gen_label && Check(TokenKind::kColon)) {
      diag_.Error(CurrentLoc(),
                  "cannot have both a generate block label and a block name");
    }
  };

  // Parse the body of a `begin ... end` generate block, including an
  // optional `: name` and the matching trailing `: name`.
  auto parse_begin_body = [&]() {
    consume_begin_name();
    while (!Check(TokenKind::kKwEnd) && !AtEnd()) {
      ParseModuleItem(body);
    }
    Expect(TokenKind::kKwEnd);
    if (Match(TokenKind::kColon)) Match(TokenKind::kIdentifier);
  };

  if (Match(TokenKind::kKwBegin)) {
    parse_begin_body();
  } else {
    ParseModuleItem(body);
  }
}

void Parser::ParseGenerateRegion(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwGenerate);

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
  Match(TokenKind::kKwGenvar);
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
