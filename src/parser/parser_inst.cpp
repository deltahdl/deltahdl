#include "parser/parser.h"

namespace delta {

ModuleItem* Parser::ParseModuleInst(const Token& module_tok) {
  return ParseModuleInstList(module_tok, nullptr);
}

ModuleItem* Parser::ParseModuleInstList(
    const Token& module_tok, std::vector<ModuleItem*>* extra_items) {
  // A.4.1.1: parameter_value_assignment shared by all instances
  std::vector<std::pair<std::string_view, Expr*>> params;
  if (Match(TokenKind::kHash)) {
    ParseParamValueAssignment(params);
  }

  auto parse_one_instance = [&]() -> ModuleItem* {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kModuleInst;
    item->loc = module_tok.loc;
    item->inst_module = module_tok.text;
    item->inst_params = params;
    item->inst_name = Expect(TokenKind::kIdentifier).text;
    // Instance array range: inst_name [left:right] or [size] (§23.3.2)
    if (Check(TokenKind::kLBracket)) {
      Consume();
      item->inst_range_left = ParseExpr();
      if (Match(TokenKind::kColon)) {
        item->inst_range_right = ParseExpr();
      }
      Expect(TokenKind::kRBracket);
    }
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      ParsePortConnection(item);
      while (Match(TokenKind::kComma)) {
        ParsePortConnection(item);
      }
    }
    Expect(TokenKind::kRParen);
    return item;
  };

  auto* first = parse_one_instance();
  if (extra_items) extra_items->push_back(first);
  // A.4.1.1: { , hierarchical_instance }
  while (Match(TokenKind::kComma)) {
    auto* next = parse_one_instance();
    if (extra_items) extra_items->push_back(next);
  }
  Expect(TokenKind::kSemicolon);
  return first;
}

void Parser::ParseParenList(std::vector<Expr*>& out) {
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    out.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      out.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen);
}

// A.4.1.1: Parse parameter_value_assignment contents inside #( ... )
// Handles both ordered and named parameter assignments.
void Parser::ParseParamValueAssignment(
    std::vector<std::pair<std::string_view, Expr*>>& out) {
  Expect(TokenKind::kLParen);
  if (!Check(TokenKind::kRParen)) {
    if (Check(TokenKind::kDot)) {
      // Named parameter assignments: .name(expr) { , .name(expr) }
      do {
        Expect(TokenKind::kDot);
        auto name = Expect(TokenKind::kIdentifier);
        Expect(TokenKind::kLParen);
        Expr* expr = nullptr;
        if (!Check(TokenKind::kRParen)) {
          expr = ParseExpr();
        }
        Expect(TokenKind::kRParen);
        out.push_back({name.text, expr});
      } while (Match(TokenKind::kComma));
    } else {
      // Ordered parameter assignments: expr { , expr }
      out.push_back({{}, ParseExpr()});
      while (Match(TokenKind::kComma)) {
        out.push_back({{}, ParseExpr()});
      }
    }
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParsePortConnection(ModuleItem* item) {
  ParseAttributes();  // §5.12: attribute on port connection
  if (Check(TokenKind::kDotStar)) {
    // .* wildcard port connection (§23.3.2.4)
    Consume();
    item->inst_wildcard = true;
    return;
  }
  if (Match(TokenKind::kDot)) {
    auto name = Expect(TokenKind::kIdentifier);
    // A.4.1.1: [ ( [ expression ] ) ] — parentheses are optional
    if (Match(TokenKind::kLParen)) {
      Expr* expr = nullptr;
      if (!Check(TokenKind::kRParen)) {
        expr = ParseExpr();
      }
      Expect(TokenKind::kRParen);
      item->inst_ports.push_back({name.text, expr});
    } else {
      // .name shorthand — implicit connection (§23.3.2.3)
      item->inst_ports.push_back({name.text, nullptr});
    }
  } else {
    // Ordered port: blank position (empty expression) or expression
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      item->inst_ports.push_back({{}, nullptr});
    } else {
      item->inst_ports.push_back({{}, ParseExpr()});
    }
  }
}

// §10.3.4: Check if a token is a strength-0 keyword.
static bool IsStr0Token(TokenKind k) {
  switch (k) {
    case TokenKind::kKwSupply0:
    case TokenKind::kKwStrong0:
    case TokenKind::kKwPull0:
    case TokenKind::kKwWeak0:
    case TokenKind::kKwHighz0:
      return true;
    default:
      return false;
  }
}

// §10.3.4: Parse drive strength pair. Called after '(' when first token is
// a strength keyword. Sets s0 (strength for value 0) and s1 (value 1).
void Parser::ParseDriveStrength(uint8_t& s0, uint8_t& s1) {
  if (IsStr0Token(CurrentToken().kind)) {
    s0 = ParseStrength0();
    Expect(TokenKind::kComma);
    s1 = ParseStrength1();
  } else {
    s1 = ParseStrength1();
    Expect(TokenKind::kComma);
    s0 = ParseStrength0();
  }
}

// §10.3.4: Check if a token is a drive strength keyword.
static bool IsDriveStrengthToken(TokenKind k) {
  switch (k) {
    case TokenKind::kKwSupply0:
    case TokenKind::kKwStrong0:
    case TokenKind::kKwPull0:
    case TokenKind::kKwWeak0:
    case TokenKind::kKwHighz0:
    case TokenKind::kKwSupply1:
    case TokenKind::kKwStrong1:
    case TokenKind::kKwPull1:
    case TokenKind::kKwWeak1:
    case TokenKind::kKwHighz1:
      return true;
    default:
      return false;
  }
}

ModuleItem* Parser::ParseContinuousAssign() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kContAssign;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwAssign);
  // §10.3.4: Optional drive strength: assign (strong0, weak1) ...
  if (Check(TokenKind::kLParen)) {
    auto saved = lexer_.SavePos();
    Consume();  // '('
    if (IsDriveStrengthToken(CurrentToken().kind)) {
      ParseDriveStrength(item->drive_strength0, item->drive_strength1);
      Expect(TokenKind::kRParen);
    } else {
      lexer_.RestorePos(saved);
    }
  }
  // Optional delay3: assign #(rise, fall, decay) or assign #delay (§10.3.3)
  if (Check(TokenKind::kHash)) {
    Consume();
    if (Match(TokenKind::kLParen)) {
      item->assign_delay = ParseMinTypMaxExpr();
      if (Match(TokenKind::kComma)) {
        item->assign_delay_fall = ParseMinTypMaxExpr();
        if (Match(TokenKind::kComma))
          item->assign_delay_decay = ParseMinTypMaxExpr();
      }
      Expect(TokenKind::kRParen);
    } else {
      item->assign_delay = ParsePrimaryExpr();
    }
  }
  item->assign_lhs = ParseExpr();
  Expect(TokenKind::kEq);
  item->assign_rhs = ParseExpr();
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseAlias() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAlias;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwAlias);
  item->alias_nets.push_back(ParseExpr());
  while (Match(TokenKind::kEq)) {
    item->alias_nets.push_back(ParseExpr());
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseAlwaysBlock(AlwaysKind kind) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAlwaysBlock;
  item->always_kind = kind;
  item->loc = CurrentLoc();
  Consume();  // always / always_comb / always_ff / always_latch

  if (Check(TokenKind::kAt)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      // @* — implicit sensitivity (§9.4.2.2)
    } else if (Check(TokenKind::kLParen)) {
      Consume();
      if (Match(TokenKind::kStar)) {
        // @(*) — implicit sensitivity (§9.4.2.2)
      } else {
        item->sensitivity = ParseEventList();
      }
      Expect(TokenKind::kRParen);
    }
  }

  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseInitialBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kInitialBlock;
  item->loc = CurrentLoc();
  Consume();  // initial
  item->body = ParseStmt();
  return item;
}

ModuleItem* Parser::ParseFinalBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFinalBlock;
  item->loc = CurrentLoc();
  Consume();  // final
  item->body = ParseStmt();
  return item;
}

Token Parser::ExpectIdentifier() {
  if (CheckIdentifier()) {
    return Consume();
  }
  auto tok = CurrentToken();
  diag_.Error(tok.loc, "expected identifier, got " +
                           std::string(TokenKindName(tok.kind)));
  return tok;
}

bool Parser::CheckIdentifier() {
  return Check(TokenKind::kIdentifier) || Check(TokenKind::kEscapedIdentifier);
}

}  // namespace delta
