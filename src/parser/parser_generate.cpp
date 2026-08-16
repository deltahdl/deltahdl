#include "parser/parser.h"

namespace delta {

// Answers whether tk closes a construct a generate region can stand inside.
// A.4.2 gives `generate_region ::= generate { generate_item } endgenerate`, and
// the four productions that reach generate_region are A.1.4's
// non_port_module_item, A.1.6's non_port_interface_item, A.1.7's
// program_generate_item and A.1.8's checker_generate_item, so a region stands
// directly in a module, an interface, a program or a checker and in nothing
// else. §27.3 is narrower than the grammar here -- "Generate regions do not
// nest, and they may only occur directly within a module" -- and the three
// keywords beyond endmodule are what the grammar admits.
static bool ClosesGenerateRegionEnclosure(TokenKind tk) {
  return tk == TokenKind::kKwEndmodule || tk == TokenKind::kKwEndinterface ||
         tk == TokenKind::kKwEndprogram || tk == TokenKind::kKwEndchecker;
}

// Answers whether tk closes a construct a generate block can stand inside.
// A.4.2 writes generate_block in three productions only:
// loop_generate_construct, if_generate_construct and case_generate_item. The
// first two end with it, so what follows a block there comes from whatever
// holds the construct: a generate_region, closed by endgenerate; an enclosing
// generate_block, closed by the `end` Parser::ParseGenerateBody tests first;
// or one of the four declarations above. The third is case_generate_item,
// whose case_generate_construct is closed by endcase.
//
// `else` is left out although A.4.2 writes it between the two generate_blocks
// of if_generate_construct, because it continues that production rather than
// closing one, and asking for it needs to know an if_generate_construct is
// open. #3164 records the reports a generate block left open before an `else`
// still draws.
static bool ClosesGenerateBlockEnclosure(TokenKind tk) {
  return ClosesGenerateRegionEnclosure(tk) || tk == TokenKind::kKwEndgenerate ||
         tk == TokenKind::kKwEndcase;
}

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
    bool committed = Match(TokenKind::kColon) && Check(TokenKind::kKwBegin);
    if (!committed) {
      lexer_.RestorePos(saved);
      return false;
    }
    out_label = ident.text;
    return true;
  };
  bool has_gen_label = detect_gen_label();

  // A bare (non-`begin`) generate body is a single module item.
  if (!Match(TokenKind::kKwBegin)) {
    ParseModuleItem(body);
    return;
  }

  // Consume the optional `: name` block name at the head of the `begin` block,
  // diagnosing a conflict with a generate-block label. A generate-block label
  // suppresses (and conflicts with) an explicit block name, so the `Match`
  // that would consume the name is guarded behind `!has_gen_label`.
  if (has_gen_label && Check(TokenKind::kColon)) {
    diag_.Error(CurrentLoc(),
                "cannot have both a generate block label and a block name",
                Subclause("9.3.5"));
  } else if (!has_gen_label && Match(TokenKind::kColon) && CheckIdentifier()) {
    out_label = Consume().text;
  }

  // Parse the items, then the matching `end` and its optional trailing
  // `: name`. Stop at a token that closes an enclosing construct as well as at
  // `end`: without that stop Parser::ParseModuleItem reports the token as a
  // stray item and Parser::SynchronizeWithProgress consumes it, so a block left
  // open before an `endgenerate` swallowed it and then the `endmodule` behind
  // it, and the report below could only ever fire at end of input.
  while (!Check(TokenKind::kKwEnd) && !AtEnd() &&
         !ClosesGenerateBlockEnclosure(CurrentToken().kind)) {
    ParseModuleItem(body);
  }
  // Leave the token for the enclosing production when it is one of the closers,
  // which is what lets the generate region find its endgenerate and the case
  // construct its endcase. Expect reports without consuming, so it survives.
  Expect(TokenKind::kKwEnd, Subclause("27.3"));
  if (Match(TokenKind::kColon)) Match(TokenKind::kIdentifier);
}

void Parser::ParseGenerateRegion(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwGenerate, Subclause("27.3"));

  if (in_generate_region_) {
    diag_.Error(loc, "generate regions shall not nest", Subclause("27.3"));
  }
  bool saved = in_generate_region_;
  in_generate_region_ = true;
  // Stop at the keyword closing the declaration the region stands in as well as
  // at `endgenerate`, for the reason Parser::ParseGenerateBody above stops at
  // one: without it a region left open before an `endmodule` had
  // Parser::ParseModuleItem report that keyword as a stray item and
  // Parser::SynchronizeWithProgress consume it, so the report below stood at
  // end of input and Parser::ParseModuleDecl reported the `endmodule` it never
  // saw. Two reports for one missing `endgenerate`, neither naming where it
  // should have been.
  while (!Check(TokenKind::kKwEndgenerate) && !AtEnd() &&
         !ClosesGenerateRegionEnclosure(CurrentToken().kind)) {
    ParseModuleItem(items);
  }
  in_generate_region_ = saved;
  // Leave the token for the enclosing production when it is one of the closers,
  // which is what lets the module find its endmodule. Expect reports without
  // consuming, so it survives.
  Expect(TokenKind::kKwEndgenerate, Subclause("27.3"));
}

ModuleItem* Parser::ParseGenerateFor() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateFor;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFor, Subclause("27.4"));
  Expect(TokenKind::kLParen, Subclause("27.4"));
  Match(TokenKind::kKwGenvar);
  item->gen_init = ParseAssignmentOrExprStmt();
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("27.4"));
  item->gen_step = ParseAssignmentOrExprNoSemi();
  Expect(TokenKind::kRParen, Subclause("27.4"));
  ParseGenerateBody(item->gen_body, item->name);
  return item;
}

ModuleItem* Parser::ParseGenerateIf() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateIf;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwIf, Subclause("27.5"));
  Expect(TokenKind::kLParen, Subclause("27.5"));
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("27.5"));
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
  Expect(TokenKind::kColon, Subclause("27.5"));
}

ModuleItem* Parser::ParseGenerateCase() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateCase;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCase, Subclause("27.5"));
  Expect(TokenKind::kLParen, Subclause("27.5"));
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("27.5"));
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    GenerateCaseItem ci;
    ParseGenerateCaseLabel(ci);
    ParseGenerateBody(ci.body, ci.label);
    item->gen_case_items.push_back(std::move(ci));
  }
  Expect(TokenKind::kKwEndcase, Subclause("27.5"));
  return item;
}

}  // namespace delta
