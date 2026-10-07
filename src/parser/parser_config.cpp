#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

namespace delta {

void Parser::ParseDesignStatement(ConfigDecl* decl) {
  Expect(TokenKind::kKwDesign, Subclause("33.4.1.1"));
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    // A token that is not a cell_identifier (e.g. the 'endconfig' keyword after
    // a design_statement whose terminating ';' is missing) ends the cell list.
    // Stop so the Expect(';') below reports it instead of spinning. Asking what
    // the token is answers that directly; comparing the lexer's position before
    // and against after does not, because the lexer reads ahead of the token
    // the parser is on, so consuming a cell_identifier need not move it.
    if (!CheckIdentifier()) break;
    Token first = ExpectIdentifier(Subclause("33.4.1.1"));
    std::string_view lib;
    // §33.4.1.1 writes an entry as `[ library_identifier . ] cell_identifier`,
    // so the position recorded is the cell_identifier's. A report about a cell
    // no library holds is about the cell, and the library_identifier the entry
    // may or may not carry would put that report in a different column of the
    // same line for the two spellings.
    Token cell = first;
    if (Match(TokenKind::kDot)) {
      lib = first.text;
      cell = ExpectIdentifier(Subclause("33.4.1.1"));
    }
    decl->design_cells.push_back(ConfigDesignCell{lib, cell.text, cell.loc});
  }
  Expect(TokenKind::kSemicolon, Subclause("33.4.1.1"));
}

void Parser::ParseLiblistClause(ConfigRule* rule) {
  Expect(TokenKind::kKwLiblist, Subclause("33.4.1.5"));
  while (CheckIdentifier() && !Check(TokenKind::kSemicolon) && !AtEnd()) {
    rule->liblist.push_back(ExpectIdentifier(Subclause("33.4.1.5")).text);
  }
}

// Parses one named_parameter_assignment: '.' parameter_identifier
// '(' [ param_expression ] ')'. The parameter expression is optional, so an
// empty override '.p()' is accepted.
void Parser::ParseNamedParamAssignment(ConfigRule* rule) {
  Expect(TokenKind::kDot, Subclause("33.4.3"));
  auto pname = ExpectIdentifier(Subclause("33.4.3")).text;
  Expect(TokenKind::kLParen, Subclause("33.4.3"));
  Expr* val = nullptr;
  if (!Check(TokenKind::kRParen)) {
    val = ParseExpr();
  }
  Expect(TokenKind::kRParen, Subclause("33.4.3"));
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
  auto first = ExpectIdentifier(Subclause("33.4.1.6")).text;
  if (Check(TokenKind::kDot) && !DotOpensNamedParamAssignment()) {
    Consume();
    rule->use_lib = first;
    rule->use_cell = ExpectIdentifier(Subclause("33.4.1.6")).text;
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
  auto use_loc = CurrentLoc();
  Expect(TokenKind::kKwUse, Subclause("33.4.1.6"));

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
    Expect(TokenKind::kLParen, Subclause("33.4.3"));
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
    Expect(TokenKind::kRParen, Subclause("33.4.3"));
  }

  if (Match(TokenKind::kColon) && Check(TokenKind::kKwConfig)) {
    Consume();
    rule->use_config = true;
  }

  // A.1.5 gives use_clause three forms, and each names something: a cell, a
  // list of named_parameter_assignment, or a cell with such a list. §33.4.1.6
  // says what the clause is for, naming the library and cell that a selected
  // cell or instance binds to, and a `use` followed by its terminator, or by
  // the `: config` suffix alone, names nothing.
  if (rule->use_cell.empty() && rule->use_params.empty() &&
      !rule->use_param_reset_all) {
    diag_.Error(use_loc,
                "use clause names a cell, a parameter assignment, or both",
                Subclause("A.1.5"));
  }
}

// The pieces of config parsing that ParseConfigRule and ParseConfigDecl hand
// off, kept out of Parser's declaration.
struct ParserConfigHelpers {
  // Every config_rule_statement pairs a selection clause with an expansion
  // clause: an inst_clause or a cell_clause is legal only when followed by a
  // liblist_clause or a use_clause. A bare 'instance <path>;' or 'cell
  // <name>;' matches no grammar alternative.
  static void SelectionExpansion(Parser& p, ConfigRule* rule,
                                 std::string_view selection) {
    if (p.Check(TokenKind::kKwLiblist)) {
      p.ParseLiblistClause(rule);
    } else if (p.Check(TokenKind::kKwUse)) {
      p.ParseUseClause(rule);
    } else {
      p.diag_.Error(
          p.CurrentLoc(),
          std::format("{} selection requires a 'liblist' or 'use' clause",
                      selection),
          Subclause("33.4.1"));
    }
  }

  // Syntax 33-4 (printed page 938) opens a config_declaration with
  // `{ local_parameter_declaration ; }`, and A.2.1.1 gives that declaration a
  // data_type_or_implicit and a list_of_param_assignments, so `localparam int
  // S = 24, T = 8;` is as much a config's as `localparam S = 24;`. They are
  // read as any localparam declaration is, and each value assignment is kept.
  static void LocalParams(Parser& p, ConfigDecl* decl) {
    // Check(kKwLocalparam) is already false at EOF (the current token is
    // kEof), so an explicit !AtEnd() guard would be redundant here.
    while (p.Check(TokenKind::kKwLocalparam)) {
      std::vector<ModuleItem*> items;
      p.ParseParamDecl(items);
      for (auto* item : items) {
        if (item->kind != ModuleItemKind::kParamDecl) continue;
        decl->local_params.emplace_back(item->name, item->init_expr);
      }
    }
  }

  // Reports and discards a duplicate 'design' statement, skipping tokens up
  // to (and including) its terminating semicolon.
  static void SkipDuplicateDesign(Parser& p, const ConfigDecl* decl) {
    p.diag_.Error(
        p.CurrentLoc(),
        std::format("duplicate 'design' statement in config '{}'", decl->name),
        Subclause("33.4.1.1"));
    p.Consume();
    while (!p.Check(TokenKind::kSemicolon) &&
           !p.Check(TokenKind::kKwEndconfig) && !p.AtEnd()) {
      p.Consume();
    }
    // Match consumes the terminating ';' iff present, equivalent to the
    // guarded 'if (Check(kSemicolon)) Consume()' but without a nested branch.
    p.Match(TokenKind::kSemicolon);
  }

  // The config_rule_statements up to 'endconfig', a duplicate 'design'
  // statement among them reported and skipped.
  static void Rules(Parser& p, ConfigDecl* decl) {
    while (!p.Check(TokenKind::kKwEndconfig) && !p.AtEnd()) {
      if (p.Check(TokenKind::kKwDesign)) {
        SkipDuplicateDesign(p, decl);
        continue;
      }
      auto before = p.lexer_.SavePos().pos;
      decl->rules.push_back(p.ParseConfigRule());
      // A token that starts no config_rule (e.g. the 'use' of an illegal
      // 'default use ...', already diagnosed) leaves the cursor unmoved. Stop
      // so the Expect(kKwEndconfig) after the rules reports it instead of
      // spinning.
      if (p.lexer_.SavePos().pos == before) break;
    }
  }
};

ConfigRule* Parser::ParseConfigRule() {
  auto* rule = arena_.Create<ConfigRule>();
  // Taken before the first token is consumed, so the position is the
  // 'default', 'instance' or 'cell' keyword the clause opens with rather than
  // whatever the clause selects.
  rule->loc = CurrentLoc();
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    rule->kind = ConfigRuleKind::kDefault;
    // §33.4.1.2 (printed page 938) bars a use expansion clause (§33.4.1.6)
    // from a default selection clause. The rule is reported
    // under that subclause, once, and the use clause is still read to its end
    // so the rules after it parse as rules.
    if (Check(TokenKind::kKwUse)) {
      diag_.Error(CurrentLoc(),
                  "a default selection clause expands only through a liblist "
                  "clause, not through a use clause",
                  Subclause("33.4.1.2"));
      ParseUseClause(rule);
    } else {
      ParseLiblistClause(rule);
    }
  } else if (Check(TokenKind::kKwInstance)) {
    Consume();
    rule->kind = ConfigRuleKind::kInstance;
    rule->inst_path = ParseDottedPath();
    ParserConfigHelpers::SelectionExpansion(*this, rule, "instance");
  } else if (Check(TokenKind::kKwCell)) {
    Consume();
    rule->kind = ConfigRuleKind::kCell;
    auto first = ExpectIdentifier(Subclause("33.4.1.4")).text;
    if (Match(TokenKind::kDot)) {
      rule->cell_lib = first;
      rule->cell_name = ExpectIdentifier(Subclause("33.4.1.4")).text;
    } else {
      rule->cell_name = first;
    }
    ParserConfigHelpers::SelectionExpansion(*this, rule, "cell");
  }
  Expect(TokenKind::kSemicolon, Subclause("33.4.1"));
  return rule;
}

ConfigDecl* Parser::ParseConfigDecl() {
  auto* decl = arena_.Create<ConfigDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwConfig, Subclause("33.4.1"));
  decl->name = Expect(TokenKind::kIdentifier, Subclause("33.4.1")).text;
  Expect(TokenKind::kSemicolon, Subclause("33.4.1"));

  ParserConfigHelpers::LocalParams(*this, decl);

  bool has_design = false;
  if (Check(TokenKind::kKwDesign)) {
    ParseDesignStatement(decl);
    has_design = true;
  } else if (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    diag_.Error(CurrentLoc(), "expected 'design' statement in config",
                Subclause("33.4.1.1"));
  }

  ParserConfigHelpers::Rules(*this, decl);

  if (!has_design) {
    diag_.Error(
        decl->range.start,
        std::format("config '{}' is missing a 'design' statement", decl->name),
        Subclause("33.4.1.1"));
  }

  Expect(TokenKind::kKwEndconfig, Subclause("33.4.1"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
