#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

bool Parser::IsTimingCheckName(std::string_view name) {
  return name == "$setup" || name == "$hold" || name == "$setuphold" ||
         name == "$recovery" || name == "$removal" || name == "$recrem" ||
         name == "$width" || name == "$period" || name == "$skew" ||
         name == "$nochange" || name == "$timeskew" || name == "$fullskew";
}

ModuleItem* Parser::ParseSpecifyBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecifyBlock;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecify, Subclause("30.3"));

  while (!Check(TokenKind::kKwEndspecify) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseSpecifyItem(item->specify_items);
    if (lexer_.SavePos().pos == before) break;
  }
  Expect(TokenKind::kKwEndspecify, Subclause("30.3"));
  return item;
}

Expr* Parser::ParsePathpulseLimits(Expr*& error_limit) {
  if (!Check(TokenKind::kLParen)) {
    diag_.Error(CurrentLoc(),
                "a PATHPULSE$ specparam's limits are written in parentheses",
                Subclause("A.2.4"));
    return ParseMinTypMaxExpr();
  }
  Consume();
  Expr* reject = ParseMinTypMaxExpr();
  if (Match(TokenKind::kComma)) error_limit = ParseMinTypMaxExpr();
  Expect(TokenKind::kRParen, Subclause("30.7.1"));
  return reject;
}

void Parser::ParseSpecparamDecl(std::vector<ModuleItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam, Subclause("6.20.5"));

  Expr* packed_left = nullptr;
  Expr* packed_right = nullptr;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    packed_left = ParseExpr();
    Expect(TokenKind::kColon, Subclause("6.20.5"));
    packed_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("6.20.5"));
  }

  auto parse_one = [&]() {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kSpecparam;
    item->loc = kw_loc;
    item->data_type.packed_dim_left = packed_left;
    item->data_type.packed_dim_right = packed_right;
    item->name = Expect(TokenKind::kIdentifier, Subclause("6.20.5")).text;
    Expect(TokenKind::kEq, Subclause("6.20.5"));
    Expr* error_limit = nullptr;
    item->init_expr = item->name.starts_with("PATHPULSE$")
                          ? ParsePathpulseLimits(error_limit)
                          : ParseMinTypMaxExpr();
    items.push_back(item);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon, Subclause("6.20.5"));
}

void Parser::ParseSpecifyItem(std::vector<SpecifyItem*>& items) {
  auto skip_to_item_end = [&]() {
    while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
           !Check(TokenKind::kKwEndspecify) &&
           !Check(TokenKind::kKwEndmodule)) {
      Consume();
    }
    Match(TokenKind::kSemicolon);
  };

  if (Check(TokenKind::kKwPulsestyleOnevent) ||
      Check(TokenKind::kKwPulsestyleOndetect)) {
    items.push_back(ParsePulsestyleDecl());
    return;
  }

  if (Check(TokenKind::kKwShowcancelled) ||
      Check(TokenKind::kKwNoshowcancelled)) {
    items.push_back(ParseShowcancelledDecl());
    return;
  }

  if (Check(TokenKind::kKwSpecparam)) {
    ParseSpecparamInSpecify(items);
    return;
  }

  if (Check(TokenKind::kSystemIdentifier) &&
      IsTimingCheckName(CurrentToken().text)) {
    items.push_back(ParseTimingCheck());
    return;
  }
  if (Check(TokenKind::kSystemIdentifier)) {
    diag_.Error(CurrentLoc(), "system task cannot appear in specify block",
                Subclause("31.2"));
    skip_to_item_end();
    return;
  }

  if (Check(TokenKind::kKwIfnone)) {
    items.push_back(ParseIfnonePathDecl());
    return;
  }
  if (Check(TokenKind::kKwIf)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("30.4.4"));
    auto* cond = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("30.4.4"));
    items.push_back(ParseConditionalPathDecl(cond));
    return;
  }

  if (Check(TokenKind::kLParen)) {
    items.push_back(ParseSpecifyPathDecl());
    return;
  }

  diag_.Error(CurrentLoc(), "unexpected token in specify block",
              Subclause("30.3"));
  skip_to_item_end();
}

static bool IsZorX(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z';
}

static bool IsZeroOrOne(char c) { return c == '0' || c == '1'; }

static bool IsTwoCharEdgeDescriptor(std::string_view text) {
  if (text.size() != 2) return false;
  if (IsZorX(text[0]) && IsZeroOrOne(text[1])) return true;
  return IsZeroOrOne(text[0]) && IsZeroOrOne(text[1]) && text[0] != text[1];
}

static bool IsSingleBinaryDigit(std::string_view text) {
  return text.size() == 1 && IsZeroOrOne(text[0]);
}

static bool IsSingleZorX(std::string_view text) {
  return text.size() == 1 && IsZorX(text[0]);
}

static void CheckEdgeDescriptorCount(DiagEngine& diag, SourceLoc list_loc,
                                     std::size_t count) {
  if (count == 0) {
    diag.Error(list_loc,
               "edge-control specifier requires at least one edge_descriptor",
               Subclause("31.5"));
  }
  if (count > 6) {
    diag.Error(list_loc,
               "edge-control specifier accepts at most six edge_descriptors",
               Subclause("31.5"));
  }
}

void Parser::ParseSplitEdgeDescriptor(
    char first, SourceLoc tok_loc,
    std::vector<std::pair<char, char>>& descriptors) {
  Consume();
  auto next_text = CurrentToken().text;
  auto next_loc = CurrentLoc();
  if (!Check(TokenKind::kIdentifier) || !IsSingleZorX(next_text)) {
    diag_.Error(tok_loc, "invalid edge_descriptor", Subclause("31.5"));
    return;
  }
  if (next_loc.line == tok_loc.line && next_loc.column == tok_loc.column + 1) {
    descriptors.push_back({first, next_text[0]});
  } else {
    diag_.Error(tok_loc, "edge_descriptor may not contain embedded spaces",
                Subclause("31.5"));
  }
  Consume();
}

void Parser::ParseEdgeDescriptorList(
    std::vector<std::pair<char, char>>& descriptors) {
  auto list_loc = CurrentLoc();
  do {
    if (Check(TokenKind::kRBracket)) break;
    auto text = CurrentToken().text;
    auto tok_loc = CurrentLoc();

    if ((Check(TokenKind::kIntLiteral) || Check(TokenKind::kIdentifier)) &&
        IsTwoCharEdgeDescriptor(text)) {
      descriptors.push_back({text[0], text[1]});
      Consume();
    } else if (Check(TokenKind::kIntLiteral) && IsSingleBinaryDigit(text)) {
      ParseSplitEdgeDescriptor(text[0], tok_loc, descriptors);
    } else {
      diag_.Error(tok_loc, "invalid edge_descriptor", Subclause("31.5"));
      Consume();
    }
  } while (Match(TokenKind::kComma));
  CheckEdgeDescriptorCount(diag_, list_loc, descriptors.size());
  Expect(TokenKind::kRBracket, Subclause("31.5"));
}

SpecifyEdge Parser::ParseSpecifyEdge(
    std::vector<std::pair<char, char>>* edge_descriptors) {
  if (Check(TokenKind::kKwPosedge)) {
    Consume();
    return SpecifyEdge::kPosedge;
  }
  if (Check(TokenKind::kKwNegedge)) {
    Consume();
    return SpecifyEdge::kNegedge;
  }
  if (Check(TokenKind::kKwEdge)) {
    Consume();
    if (edge_descriptors && Match(TokenKind::kLBracket)) {
      ParseEdgeDescriptorList(*edge_descriptors);
    }
    return SpecifyEdge::kEdge;
  }
  return SpecifyEdge::kNone;
}

SpecifyTerminal Parser::ParseSpecifyTerminal() {
  SpecifyTerminal term;
  term.name = ExpectIdentifier(Subclause("30.4")).text;

  if (Match(TokenKind::kDot)) {
    term.interface_name = term.name;
    term.name = ExpectIdentifier(Subclause("25.6")).text;
  }

  if (Match(TokenKind::kLBracket)) {
    term.range_left = ParseExpr();
    if (Match(TokenKind::kColon)) {
      term.range_kind = SpecifyRangeKind::kPartSelect;
      term.range_right = ParseExpr();
    } else if (Match(TokenKind::kPlusColon)) {
      term.range_kind = SpecifyRangeKind::kPlusIndexed;
      term.range_right = ParseExpr();
    } else if (Match(TokenKind::kMinusColon)) {
      term.range_kind = SpecifyRangeKind::kMinusIndexed;
      term.range_right = ParseExpr();
    } else {
      term.range_kind = SpecifyRangeKind::kBitSelect;
    }
    Expect(TokenKind::kRBracket, Subclause("30.4"));
  }

  return term;
}

void Parser::ParsePathPorts(std::vector<SpecifyTerminal>& ports) {
  if (Check(TokenKind::kLBrace)) {
    diag_.Error(CurrentLoc(),
                "path terminals are listed with commas alone; a concatenation "
                "is no specify terminal",
                Subclause("A.7.3"));
    Consume();
    SkipBraceBlock(lexer_);
    return;
  }
  ports.push_back(ParseSpecifyTerminal());
  while (Match(TokenKind::kComma)) {
    ports.push_back(ParseSpecifyTerminal());
  }
}

void Parser::ParsePathDelayList(std::vector<Expr*>& delays) {
  delays.push_back(ParseMinTypMaxExpr());
  while (Match(TokenKind::kComma)) {
    delays.push_back(ParseMinTypMaxExpr());
  }
}

bool Parser::TryParseParenthesizedPathDelays(std::vector<Expr*>& delays) {
  if (!Check(TokenKind::kLParen)) return false;
  auto saved = lexer_.SavePos();
  uint32_t errors_before = diag_.ErrorCount();
  Consume();
  std::vector<Expr*> list;
  ParsePathDelayList(list);
  bool clean = diag_.ErrorCount() == errors_before;
  if (clean && Match(TokenKind::kRParen)) {
    if (Check(TokenKind::kSemicolon)) {
      delays = std::move(list);
      return true;
    }
    lexer_.RestorePos(saved);
    return false;
  }
  Expect(TokenKind::kRParen, Subclause("30.5"));
  delays = std::move(list);
  return true;
}

void Parser::ParsePathDelays(std::vector<Expr*>& delays) {
  auto loc = CurrentLoc();
  if (!TryParseParenthesizedPathDelays(delays)) {
    ParsePathDelayList(delays);
  }

  auto n = delays.size();
  if (n != 1 && n != 2 && n != 3 && n != 6 && n != 12) {
    diag_.Error(loc, "path delay must have 1, 2, 3, 6, or 12 values",
                Subclause("30.5"));
  }
}

SpecifyPolarity Parser::ParseSpecifyPolarity() {
  if (Check(TokenKind::kPlus)) {
    Consume();
    return SpecifyPolarity::kPositive;
  }
  if (Check(TokenKind::kMinus)) {
    Consume();
    return SpecifyPolarity::kNegative;
  }
  return SpecifyPolarity::kNone;
}

static void CheckParallelPathTerminalCount(DiagEngine& diag, SourceLoc loc,
                                           const SpecifyPathDecl& path) {
  if (path.path_kind == SpecifyPathKind::kParallel &&
      (path.src_ports.size() != 1 || path.dst_ports.size() != 1)) {
    diag.Error(loc,
               "parallel path '=>' requires a single source and "
               "destination terminal",
               Subclause("30.4.5"));
  }
}

static SpecifyPolarity PolarityPrefixOf(TokenKind kind) {
  if (kind == TokenKind::kPlusEq) return SpecifyPolarity::kPositive;
  if (kind == TokenKind::kMinusEq) return SpecifyPolarity::kNegative;
  return SpecifyPolarity::kNone;
}

bool Parser::ParsePolarityPrefixedParallelPath(SpecifyItem* item) {
  SpecifyPolarity prefix = PolarityPrefixOf(CurrentToken().kind);
  if (item->path.polarity != SpecifyPolarity::kNone ||
      prefix == SpecifyPolarity::kNone) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();
  if (Match(TokenKind::kGt)) {
    item->path.polarity = prefix;
    item->path.path_kind = SpecifyPathKind::kParallel;
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

void Parser::ParseSpecifyPathOperator(SpecifyItem* item) {
  if (ParsePolarityPrefixedParallelPath(item)) return;
  if (Match(TokenKind::kEqGt)) {
    item->path.path_kind = SpecifyPathKind::kParallel;
    return;
  }
  if (Match(TokenKind::kStarGt)) {
    item->path.path_kind = SpecifyPathKind::kFull;
    return;
  }
  diag_.Error(CurrentLoc(),
              "path joins its source to its destination with '=>' or '*>'",
              Subclause("30.4.2"));
  if (!Check(TokenKind::kIdentifier) && !Check(TokenKind::kRParen)) Consume();
}

void Parser::ParseSpecifyPathDestination(SpecifyItem* item) {
  bool parenthesized = Match(TokenKind::kLParen);
  ParsePathPorts(item->path.dst_ports);
  if (!parenthesized) return;
  if (Match(TokenKind::kPlusColon)) {
    item->path.dst_polarity = SpecifyPolarity::kPositive;
  } else if (Match(TokenKind::kMinusColon)) {
    item->path.dst_polarity = SpecifyPolarity::kNegative;
  } else {
    item->path.dst_polarity = ParseSpecifyPolarity();
    Expect(TokenKind::kColon, Subclause("30.4.3"));
  }
  item->path.data_source = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("30.4.3"));
}

SpecifyItem* Parser::ParseSpecifyPathDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPathDecl;
  item->loc = CurrentLoc();
  item->path.loc = item->loc;

  Expect(TokenKind::kLParen, Subclause("30.4"));
  item->path.edge = ParseSpecifyEdge();
  ParsePathPorts(item->path.src_ports);

  item->path.polarity = ParseSpecifyPolarity();
  ParseSpecifyPathOperator(item);
  ParseSpecifyPathDestination(item);

  Expect(TokenKind::kRParen, Subclause("30.4"));
  Expect(TokenKind::kEq, Subclause("30.5"));
  ParsePathDelays(item->path.delays);
  Expect(TokenKind::kSemicolon, Subclause("30.4"));

  CheckParallelPathTerminalCount(diag_, item->loc, item->path);

  return item;
}

SpecifyItem* Parser::ParseConditionalPathDecl(Expr* cond) {
  auto* item = ParseSpecifyPathDecl();
  item->path.condition = cond;
  return item;
}

SpecifyItem* Parser::ParseIfnonePathDecl() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwIfnone, Subclause("30.4.4.4"));
  auto* item = ParseSpecifyPathDecl();
  item->path.is_ifnone = true;

  if (item->path.edge != SpecifyEdge::kNone ||
      item->path.data_source != nullptr) {
    diag_.Error(loc, "ifnone requires a simple path declaration",
                Subclause("30.4.4.4"));
  }
  return item;
}

SpecifyItem* Parser::ParsePulsestyleDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPulsestyle;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwPulsestyleOndetect)) {
    item->is_ondetect = true;
  }
  Consume();

  ParsePathPorts(item->path_outputs);
  Expect(TokenKind::kSemicolon, Subclause("30.7.4.1"));
  return item;
}

SpecifyItem* Parser::ParseShowcancelledDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kShowcancelled;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwNoshowcancelled)) {
    item->is_noshowcancelled = true;
  }
  Consume();

  ParsePathPorts(item->path_outputs);
  Expect(TokenKind::kSemicolon, Subclause("30.7.4.2"));
  return item;
}

static void DecodePathpulseName(SpecifyItem& sp) {
  sp.is_pathpulse = true;
  constexpr std::string_view kPrefix = "PATHPULSE$";
  std::string_view rest = sp.param_name.substr(kPrefix.size());
  if (rest.empty()) return;
  auto sep = rest.find('$');
  if (sep == std::string_view::npos) {
    sp.pathpulse_input = rest;
    return;
  }
  sp.pathpulse_input = rest.substr(0, sep);
  sp.pathpulse_output = rest.substr(sep + 1);
}

bool Parser::RefusePathpulseTerminalSelect() {
  if (!Check(TokenKind::kLBracket)) return false;
  diag_.Error(CurrentLoc(),
              "a PATHPULSE$ specparam names each terminal whole, without "
              "selecting a bit or a part of it",
              Subclause("30.7.1"));
  while (!AtEnd() && !Check(TokenKind::kEq) && !Check(TokenKind::kSemicolon)) {
    Consume();
  }
  return true;
}

void Parser::ParseSpecparamInSpecify(std::vector<SpecifyItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam, Subclause("6.20.5"));

  Expr* packed_left = nullptr;
  Expr* packed_right = nullptr;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    packed_left = ParseExpr();
    Expect(TokenKind::kColon, Subclause("6.20.5"));
    packed_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("6.20.5"));
  }

  auto parse_pathpulse_value = [&](SpecifyItem* sp) {
    DecodePathpulseName(*sp);
    sp->pathpulse_reject = ParsePathpulseLimits(sp->pathpulse_error);
    sp->param_value = sp->pathpulse_reject;
  };

  auto parse_one = [&]() {
    auto* sp = arena_.Create<SpecifyItem>();
    sp->kind = SpecifyItemKind::kSpecparam;
    sp->loc = kw_loc;
    sp->param_packed_left = packed_left;
    sp->param_packed_right = packed_right;
    sp->param_name = Expect(TokenKind::kIdentifier, Subclause("6.20.5")).text;
    bool pathpulse = sp->param_name.starts_with("PATHPULSE$");
    bool refused = pathpulse && RefusePathpulseTerminalSelect();
    Expect(TokenKind::kEq, Subclause("6.20.5"));
    if (pathpulse) {
      parse_pathpulse_value(sp);
    } else {
      sp->param_value = ParseMinTypMaxExpr();
    }
    if (!refused) items.push_back(sp);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon, Subclause("6.20.5"));
}

}  // namespace delta
