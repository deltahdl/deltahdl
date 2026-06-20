#include <format>

#include "parser/parser.h"

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

// Parses one named_parameter_assignment: '.' parameter_identifier
// '(' [ param_expression ] ')'. The parameter expression is optional, so an
// empty override '.p()' is accepted.
void Parser::ParseNamedParamAssignment(ConfigRule* rule) {
  Expect(TokenKind::kDot);
  auto pname = ExpectIdentifier().text;
  Expect(TokenKind::kLParen);
  Expr* val = nullptr;
  if (!Check(TokenKind::kRParen)) {
    val = ParseExpr();
  }
  Expect(TokenKind::kRParen);
  rule->use_params.emplace_back(pname, val);
}

void Parser::ParseUseClause(ConfigRule* rule) {
  Expect(TokenKind::kKwUse);

  // Parses a comma-separated list of named_parameter_assignment, consuming the
  // current item first and then each ', .name(...)' that follows.
  auto parse_named_param_list = [this, rule]() {
    do {
      ParseNamedParamAssignment(rule);
    } while (Match(TokenKind::kComma));
  };

  if (CheckIdentifier()) {
    // use_clause form: [ library_identifier . ] cell_identifier
    // { , named_parameter_assignment }
    auto first = ExpectIdentifier().text;
    if (Match(TokenKind::kDot)) {
      rule->use_lib = first;
      rule->use_cell = ExpectIdentifier().text;
    } else {
      rule->use_cell = first;
    }
    while (Match(TokenKind::kComma)) {
      ParseNamedParamAssignment(rule);
    }
  } else if (Check(TokenKind::kDot)) {
    // use_clause form: named_parameter_assignment
    // { , named_parameter_assignment }
    parse_named_param_list();
  }

  if (Match(TokenKind::kHash)) {
    Expect(TokenKind::kLParen);
    // An empty override list (#()) resets every parameter of the cell to its
    // module default; within a list, an override whose parentheses are empty
    // (.p()) resets that single parameter to its default. Only named
    // (.name(...)) notation is permitted here -- positional overrides are not
    // valid in a configuration.
    if (Check(TokenKind::kRParen)) {
      rule->use_param_reset_all = true;
    } else {
      parse_named_param_list();
    }
    Expect(TokenKind::kRParen);
  }

  if (Match(TokenKind::kColon) && Check(TokenKind::kKwConfig)) {
    Consume();
    rule->use_config = true;
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

  // Optional 'localparam <id> = <expr>;' declarations precede the design
  // statement and rules in a config_declaration.
  auto parse_local_params = [this, decl]() {
    while (Check(TokenKind::kKwLocalparam) && !AtEnd()) {
      Consume();
      auto pname = ExpectIdentifier().text;
      Expect(TokenKind::kEq);
      auto* val = ParseExpr();
      decl->local_params.emplace_back(pname, val);
      Expect(TokenKind::kSemicolon);
    }
  };

  // Reports and discards a duplicate 'design' statement, skipping tokens up to
  // (and including) its terminating semicolon.
  auto skip_duplicate_design = [this, decl]() {
    diag_.Error(
        CurrentLoc(),
        std::format("duplicate 'design' statement in config '{}'", decl->name));
    Consume();
    while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndconfig) &&
           !AtEnd()) {
      Consume();
    }
    if (Check(TokenKind::kSemicolon)) Consume();
  };

  parse_local_params();

  bool has_design = false;
  if (Check(TokenKind::kKwDesign)) {
    ParseDesignStatement(decl);
    has_design = true;
  } else if (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    diag_.Error(CurrentLoc(), "expected 'design' statement in config");
  }

  while (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    if (Check(TokenKind::kKwDesign)) {
      skip_duplicate_design();
      continue;
    }
    decl->rules.push_back(ParseConfigRule());
  }

  if (!has_design) {
    diag_.Error(
        decl->range.start,
        std::format("config '{}' is missing a 'design' statement", decl->name));
  }

  Expect(TokenKind::kKwEndconfig);
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
