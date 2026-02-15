#include <algorithm>

#include "parser/parser.h"

namespace delta {

// Parse: design { [lib.] cell } ;
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

// Parse: liblist { library_identifier }
void Parser::ParseLiblistClause(ConfigRule* rule) {
  Expect(TokenKind::kKwLiblist);
  while (CheckIdentifier() && !Check(TokenKind::kSemicolon) && !AtEnd()) {
    rule->liblist.push_back(ExpectIdentifier().text);
  }
}

// Parse: use [lib.] cell [:config] | use named_params [:config]
//        | use [lib.] cell named_params [:config]
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
  // Optional named parameter assignments: #(.NAME(value), ...)
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
  // Optional :config suffix (always last per BNF)
  if (Match(TokenKind::kColon)) {
    if (Check(TokenKind::kKwConfig)) {
      Consume();
      rule->use_config = true;
    }
  }
}

// Parse a single config rule statement.
ConfigRule* Parser::ParseConfigRule() {
  auto* rule = arena_.Create<ConfigRule>();
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    rule->kind = ConfigRuleKind::kDefault;
    ParseLiblistClause(rule);
  } else if (Check(TokenKind::kKwInstance)) {
    Consume();
    rule->kind = ConfigRuleKind::kInstance;
    // Hierarchical instance path: top.u1.u2
    auto first = ExpectIdentifier().text;
    std::string path(first);
    while (Match(TokenKind::kDot)) {
      path.push_back('.');
      auto next = ExpectIdentifier().text;
      path.append(next.data(), next.size());
    }
    // Store in arena so string_view remains valid.
    auto* buf = static_cast<char*>(arena_.Allocate(path.size(), 1));
    std::copy_n(path.data(), path.size(), buf);
    rule->inst_path = std::string_view(buf, path.size());
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

// Parse: config name; ... endconfig [: name]
ConfigDecl* Parser::ParseConfigDecl() {
  auto* decl = arena_.Create<ConfigDecl>();
  decl->range.start = CurrentLoc();
  Expect(TokenKind::kKwConfig);
  decl->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);

  // Optional localparam declarations.
  while (Check(TokenKind::kKwLocalparam) && !AtEnd()) {
    Consume();
    auto pname = ExpectIdentifier().text;
    Expect(TokenKind::kEq);
    auto* val = ParseExpr();
    decl->local_params.emplace_back(pname, val);
    Expect(TokenKind::kSemicolon);
  }

  // Design statement (required).
  if (Check(TokenKind::kKwDesign)) {
    ParseDesignStatement(decl);
  }

  // Config rule statements.
  while (!Check(TokenKind::kKwEndconfig) && !AtEnd()) {
    decl->rules.push_back(ParseConfigRule());
  }

  Expect(TokenKind::kKwEndconfig);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  decl->range.end = CurrentLoc();
  return decl;
}

}  // namespace delta
