#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"

namespace delta {

void Parser::ParseDesignStatement(ConfigDecl* decl) {
  Expect(TokenKind::kKwDesign, Subclause("33.4.1.1"));
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    if (!CheckIdentifier()) break;
    Token first = ExpectIdentifier(Subclause("33.4.1.1"));
    std::string_view lib;
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
  if (Check(TokenKind::kComma)) {
    diag_.Error(CurrentLoc(),
                "a use clause's first parameter assignment follows its cell "
                "with no comma",
                Subclause("A.1.5"));
  }
  while (Match(TokenKind::kComma)) {
    ParseNamedParamAssignment(rule);
  }
}

void Parser::ParseUseClause(ConfigRule* rule) {
  auto use_loc = CurrentLoc();
  Expect(TokenKind::kKwUse, Subclause("33.4.1.6"));

  auto parse_named_param_list = [this, rule]() {
    do {
      ParseNamedParamAssignment(rule);
    } while (Match(TokenKind::kComma));
  };

  if (CheckIdentifier()) {
    ParseUseClauseCell(rule);
  } else if (Check(TokenKind::kDot)) {
    parse_named_param_list();
  }

  if (Match(TokenKind::kHash)) {
    Expect(TokenKind::kLParen, Subclause("33.4.3"));
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

  if (rule->use_cell.empty() && rule->use_params.empty() &&
      !rule->use_param_reset_all) {
    diag_.Error(use_loc,
                "use clause names a cell, a parameter assignment, or both",
                Subclause("A.1.5"));
  }
}

struct ParserConfigHelpers {
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

  static void LocalParams(Parser& p, ConfigDecl* decl) {
    while (p.Check(TokenKind::kKwLocalparam)) {
      std::vector<ModuleItem*> items;
      p.ParseParamDecl(items);
      for (auto* item : items) {
        if (item->kind != ModuleItemKind::kParamDecl) continue;
        decl->local_params.push_back(
            {item->name, item->init_expr, item->data_type,
             item->data_type.kind == DataTypeKind::kVoid, item->loc});
      }
    }
  }

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
    p.Match(TokenKind::kSemicolon);
  }

  static void LateDesign(Parser& p, ConfigDecl* decl) {
    p.diag_.Error(p.CurrentLoc(),
                  std::format("config '{}' places its 'design' statement "
                              "after a config rule statement",
                              decl->name),
                  Subclause("33.4.1.1"));
    p.ParseDesignStatement(decl);
  }

  static void Rules(Parser& p, ConfigDecl* decl, bool& has_design) {
    while (!p.Check(TokenKind::kKwEndconfig) && !p.AtEnd()) {
      if (p.Check(TokenKind::kKwDesign)) {
        if (has_design) {
          SkipDuplicateDesign(p, decl);
        } else {
          LateDesign(p, decl);
          has_design = true;
        }
        continue;
      }
      auto before = p.lexer_.SavePos().pos;
      decl->rules.push_back(p.ParseConfigRule());
      if (p.lexer_.SavePos().pos == before) break;
    }
  }
};

ConfigRule* Parser::ParseConfigRule() {
  auto* rule = arena_.Create<ConfigRule>();
  rule->loc = CurrentLoc();
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    rule->kind = ConfigRuleKind::kDefault;
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
  }

  ParserConfigHelpers::Rules(*this, decl, has_design);

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
