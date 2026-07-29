#include <format>

#include "parser/parser.h"

namespace delta {

void Parser::ParseDesignStatement(ConfigDecl* decl) {
  Expect(TokenKind::kKwDesign);
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    // A token that is not a cell_identifier (e.g. the 'endconfig' keyword after
    // a design_statement whose terminating ';' is missing) ends the cell list.
    // Stop so the Expect(';') below reports it instead of spinning. Asking what
    // the token is answers that directly; comparing the lexer's position before
    // and against after does not, because the lexer reads ahead of the token
    // the parser is on, so consuming a cell_identifier need not move it.
    if (!CheckIdentifier()) break;
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

// §33.4.1.6 use_clause: `[ library_identifier . ] cell_identifier` followed by
// its named parameter assignments. Form 3 lets an assignment directly follow
// the cell_identifier with no separating comma ('use lib.cell .p(v), .q(w)'),
// any further ones being comma-separated; a leading comma
// ('use lib.cell , .p(v)') is tolerated as a lenient continuation.
// True when the '.' the parser is sitting on opens a named_parameter_assignment
// rather than separating a library from a cell. Both spellings put a '.' and an
// identifier after the first identifier of a use_clause -- `lib.cell` and
// `cell .p(v)` -- and only the parameter form has a '(' after that identifier,
// so telling them apart takes one token more of lookahead than the '.' itself.
bool Parser::DotOpensNamedParamAssignment() {
  auto saved = lexer_.SavePos();
  Consume();
  bool is_param = false;
  if (CheckIdentifier()) {
    Consume();
    is_param = Check(TokenKind::kLParen);
  }
  lexer_.RestorePos(saved);
  return is_param;
}

void Parser::ParseUseClauseCell(ConfigRule* rule) {
  auto first = ExpectIdentifier().text;
  if (Check(TokenKind::kDot) && !DotOpensNamedParamAssignment()) {
    Consume();
    rule->use_lib = first;
    rule->use_cell = ExpectIdentifier().text;
  } else {
    rule->use_cell = first;
  }
  if (Check(TokenKind::kDot)) {
    do {
      ParseNamedParamAssignment(rule);
    } while (Match(TokenKind::kComma));
    return;
  }
  while (Match(TokenKind::kComma)) {
    ParseNamedParamAssignment(rule);
  }
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
    ParseUseClauseCell(rule);
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
    // Every config_rule_statement pairs a selection clause with an expansion
    // clause: an inst_clause is legal only when followed by a liblist_clause or
    // a use_clause. A bare 'instance <path>;' matches no grammar alternative.
    if (Check(TokenKind::kKwLiblist)) {
      ParseLiblistClause(rule);
    } else if (Check(TokenKind::kKwUse)) {
      ParseUseClause(rule);
    } else {
      diag_.Error(CurrentLoc(),
                  "instance selection requires a 'liblist' or 'use' clause");
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
    // As with an inst_clause, a cell_clause is legal only when followed by a
    // liblist_clause or a use_clause; a bare 'cell <name>;' is not a
    // config_rule_statement.
    if (Check(TokenKind::kKwLiblist)) {
      ParseLiblistClause(rule);
    } else if (Check(TokenKind::kKwUse)) {
      ParseUseClause(rule);
    } else {
      diag_.Error(CurrentLoc(),
                  "cell selection requires a 'liblist' or 'use' clause");
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
    // Check(kKwLocalparam) is already false at EOF (the current token is kEof),
    // so an explicit !AtEnd() guard would be redundant here.
    while (Check(TokenKind::kKwLocalparam)) {
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
    // Match consumes the terminating ';' iff present, equivalent to the
    // guarded 'if (Check(kSemicolon)) Consume()' but without a nested branch.
    Match(TokenKind::kSemicolon);
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
    auto before = lexer_.SavePos().pos;
    decl->rules.push_back(ParseConfigRule());
    // A token that starts no config_rule (e.g. the 'use' of an illegal
    // 'default use ...', already diagnosed) leaves the cursor unmoved. Stop so
    // the Expect(kKwEndconfig) below reports it instead of spinning.
    if (lexer_.SavePos().pos == before) break;
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
