#include "parser/parser.h"

#include <format>

namespace delta {

void Parser::ParseDesignStatement(ConfigDecl* decl) {
  Expect(TokenKind::kKwDesign);
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    auto first = ExpectIdentifier().text;
    std::string_view lib;
    std::string_view cell = first;
    if (Match(TokenKind::kDot)) {
      lib = first;
      cell = ExpectIdentifier().text;
    }
    decl->design_cells.emplace_back(lib, cell);
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseLiblistClause(ConfigRule* rule) {
  Expect(TokenKind::kKwLiblist);
  while (CheckIdentifier() && !Check(TokenKind::kSemicolon) && !AtEnd()) {
    rule->liblist.push_back(ExpectIdentifier().text);
  }
}

void Parser::ParseUseClause(ConfigRule* rule) {
  Expect(TokenKind::kKwUse);
  if (CheckIdentifier()) {
    auto first = ExpectIdentifier().text;
    if (Match(TokenKind::kDot)) {
      rule->use_lib = first;
      rule->use_cell = ExpectIdentifier().text;
    } else {
      rule->use_cell = first;
    }
  }

  if (Match(TokenKind::kHash)) {
    Expect(TokenKind::kLParen);
    do {
      Expect(TokenKind::kDot);
      auto pname = ExpectIdentifier().text;
      Expect(TokenKind::kLParen);
      auto* val = ParseExpr();
      Expect(TokenKind::kRParen);
      rule->use_params.emplace_back(pname, val);
    } while (Match(TokenKind::kComma));
    Expect(TokenKind::kRParen);
  }

  if (Match(TokenKind::kColon)) {
    if (Check(TokenKind::kKwConfig)) {
      Consume();
      rule->use_config = true;
    }
  }
}

ConfigRule* Parser::ParseConfigRule() {
  auto* rule = arena_.Create<ConfigRule>();
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    rule->kind = ConfigRuleKind::kDefault;
    ParseLiblistClause(rule);
  } else if (Check(TokenKind::kKwInstance)) {
    Consume();
    rule->kind = ConfigRuleKind::kInstance;
    rule->inst_path = ParseDottedPath();
    if (Check(TokenKind::kKwLiblist)) {
      ParseLiblistClause(rule);
    } else if (Check(TokenKind::kKwUse)) {
      ParseUseClause(rule);
    }
  } else if (Check(TokenKind::kKwCell)) {
    Consume();
    rule->kind = ConfigRuleKind::kCell;
    auto first = ExpectIdentifier().text;
    if (Match(TokenKind::kDot)) {
      rule->cell_lib = first;
      rule->cell_name = ExpectIdentifier().text;
    } else {
      rule->cell_name = first;
    }
    if (Check(TokenKind::kKwLiblist)) {
      ParseLiblistClause(rule);
    } else if (Check(TokenKind::kKwUse)) {
      ParseUseClause(rule);
    }
  }
  Expect(TokenKind::kSemicolon);
  return rule;
}

ConfigDecl* Parser::ParseConfigDecl() {
  auto* decl = arena_.Create<ConfigDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwConfig);
  decl->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);

  while (Check(TokenKind::kKwLocalparam) && !AtEnd()) {
    Consume();
    auto pname = ExpectIdentifier().text;
    Expect(TokenKind::kEq);
    auto* val = ParseExpr();
    decl->local_params.emplace_back(pname, val);
    Expect(TokenKind::kSemicolon);
  }

  bool has_design = false;
  if (Check(TokenKind::kKwDesign)) {
    ParseDesignStatement(decl);
    has_design = true;
  } else if (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    diag_.Error(CurrentLoc(), "expected 'design' statement in config");
  }

  while (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    if (Check(TokenKind::kKwDesign)) {
      diag_.Error(CurrentLoc(),
                  std::format("duplicate 'design' statement in config '{}'",
                              decl->name));

      Consume();
      while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndconfig)
             && !AtEnd()) {
        Consume();
      }
      if (Check(TokenKind::kSemicolon)) Consume();
      continue;
    }
    decl->rules.push_back(ParseConfigRule());
  }

  if (!has_design) {
    diag_.Error(decl->range.start,
                std::format("config '{}' is missing a 'design' statement",
                            decl->name));
  }

  Expect(TokenKind::kKwEndconfig);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

}
