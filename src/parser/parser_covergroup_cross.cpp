#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_covergroup_internal.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

namespace {

constexpr int kCrossSetExpressionBp = 7;

void ReadOtherNamesAsCrossSets(SelectExpression* select, std::string_view label,
                               Arena& arena) {
  if (select == nullptr) return;
  ReadOtherNamesAsCrossSets(select->lhs, label, arena);
  ReadOtherNamesAsCrossSets(select->rhs, label, arena);
  if (select->kind != SelectExpressionKind::kCrossIdentifier ||
      select->cross_name == label) {
    return;
  }
  auto* name = arena.Create<Expr>();
  name->kind = ExprKind::kIdentifier;
  name->text = select->cross_name;
  name->range.start = select->loc;
  select->kind = SelectExpressionKind::kCrossSet;
  select->expr = name;
  select->cross_name = {};
}

void ReportMisplacedDollar(SourceLoc at, DiagEngine& diag) {
  diag.Error(at,
             "'$' stands for one bound of a '[ lo : hi ]' value range alone",
             Subclause("A.2.11"));
}

void NoteStrayCrossComma(bool item_due, SourceLoc at,
                         std::optional<SourceLoc>& stray) {
  if (item_due && !stray.has_value()) stray = at;
}

}  // namespace

void Parser::ParseCovergroupRangeList(
    std::vector<CovergroupValueRange>& ranges) {
  do {
    ranges.push_back(ParseCovergroupValueRange());
  } while (Match(TokenKind::kComma));
}

CovergroupValueRange Parser::ParseCovergroupValueRange() {
  CovergroupValueRange range;
  if (!Match(TokenKind::kLBracket)) {
    range.lo = ParseExpr();
    return range;
  }
  const SourceLoc kLowLoc = CurrentLoc();
  const bool kLowDollar = Match(TokenKind::kDollar);
  if (!kLowDollar) range.lo = ParseExpr();
  if (Match(TokenKind::kPlusSlashMinus)) {
    range.kind = CovergroupValueRangeKind::kAbsoluteTolerance;
    range.hi = ParseExpr();
  } else if (Match(TokenKind::kPlusPercentMinus)) {
    range.kind = CovergroupValueRangeKind::kRelativeTolerance;
    range.hi = ParseExpr();
  } else {
    range.kind = CovergroupValueRangeKind::kRange;
    Expect(TokenKind::kColon, Subclause("A.2.11"));
    const SourceLoc kHighLoc = CurrentLoc();
    if (!Match(TokenKind::kDollar)) {
      range.hi = ParseExpr();
    } else if (kLowDollar) {
      ReportMisplacedDollar(kHighLoc, diag_);
    }
  }
  if (kLowDollar && range.kind != CovergroupValueRangeKind::kRange) {
    ReportMisplacedDollar(kLowLoc, diag_);
  }
  Expect(TokenKind::kRBracket, Subclause("A.2.11"));
  return range;
}

bool Parser::AtTransRepetition() {
  if (!Check(TokenKind::kLBracket)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool repetition = Check(TokenKind::kStar) || Check(TokenKind::kArrow) ||
                    Check(TokenKind::kEq);
  lexer_.RestorePos(saved);
  return repetition;
}

TransRangeList Parser::ParseTransRangeList() {
  TransRangeList step;
  ParseCovergroupRangeList(step.items);
  if (!AtTransRepetition()) return step;
  Consume();
  if (Match(TokenKind::kStar)) {
    step.repetition = TransRepetition::kConsecutive;
  } else if (Match(TokenKind::kArrow)) {
    step.repetition = TransRepetition::kGoto;
  } else {
    Consume();
    step.repetition = TransRepetition::kNonconsecutive;
  }
  step.repeat_lo = ParseExpr();
  if (Match(TokenKind::kColon)) step.repeat_hi = ParseExpr();
  Expect(TokenKind::kRBracket, Subclause("A.2.11"));
  return step;
}

void Parser::ParseTransList(std::vector<TransSet>& sets) {
  do {
    TransSet set;
    set.loc = CurrentLoc();
    Expect(TokenKind::kLParen, Subclause("A.2.11"));
    do {
      set.steps.push_back(ParseTransRangeList());
    } while (Match(TokenKind::kEqGt));
    ExpectCoverageCloseParen();
    sets.push_back(set);
  } while (Match(TokenKind::kComma));
}

void Parser::ParseCoverCross(CovergroupBodyState& state, std::string_view label,
                             SourceLoc label_loc) {
  auto* cross = arena_.Create<CoverCrossDecl>();
  cross->loc = label.empty() ? CurrentLoc() : label_loc;
  cross->label = label;
  Consume();
  ValidateCrossItemList(cross->items);
  cross->iff = ParseCoverageIffGuard();
  TakeCoverageName(state, label, label_loc);
  CoverageSpecOrOption item;
  item.kind = CoverageSpecKind::kCoverCross;
  item.cover_cross = cross;
  state.cg->items.push_back(item);
  ParseCrossBody(*cross, state);
}

void Parser::ValidateCrossItemList(std::vector<CrossItem>& items) {
  SourceLoc start = CurrentLoc();
  bool expr_item = false;
  bool expect_item = true;
  std::optional<SourceLoc> stray_comma;
  while (!AtEnd()) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kKwIff || k == TokenKind::kLBrace ||
        k == TokenKind::kSemicolon || k == TokenKind::kKwEndgroup) {
      break;
    }
    if (k == TokenKind::kComma) {
      NoteStrayCrossComma(expect_item, Consume().loc, stray_comma);
      expect_item = true;
      continue;
    }
    if (k == TokenKind::kIdentifier && expect_item) {
      Token name = Consume();
      items.push_back({name.text, name.loc});
      expect_item = false;
      continue;
    }
    expr_item = true;
    Consume();
  }
  NoteStrayCrossComma(expect_item && !items.empty(), CurrentLoc(), stray_comma);
  if (expr_item) {
    diag_.Error(start,
                "a cross item names a coverage point or a variable; to cross "
                "an expression, give it a coverage point first",
                Subclause("19.6"));
  } else if (items.size() < 2) {
    diag_.Error(start, "a cross shall list at least two coverage points",
                Subclause("19.6"));
  }
  if (stray_comma.has_value()) {
    diag_.Error(*stray_comma,
                "a cross lists its items with one ',' between each two of "
                "them",
                Subclause("A.2.11"));
  }
}

void Parser::ParseCrossBody(CoverCrossDecl& cross, CovergroupBodyState& state) {
  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace)) {
    ReportStrayCoverageToken(CurrentToken(), diag_);
  }
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace) &&
         !AtEnd()) {
    Consume();
  }
  if (Match(TokenKind::kSemicolon) || !Match(TokenKind::kLBrace)) return;
  TypeNameScope cross_types(*this);
  known_types_.insert("CrossValType");
  known_types_.insert("CrossQueueType");
  while (!Check(TokenKind::kRBrace) && !Check(TokenKind::kKwEndgroup) &&
         !AtEnd()) {
    ParseCrossBodyItem(cross, state);
  }
  Expect(TokenKind::kRBrace, Subclause("A.2.11"));
}

void Parser::ParseCrossBodyItem(CoverCrossDecl& cross,
                                CovergroupBodyState& state) {
  ParseAttributes();
  CrossBodyItem item;
  if (Check(TokenKind::kKwFunction)) {
    item.kind = CrossBodyItemKind::kFunction;
    item.function = ParseFunctionDecl();
    cross.body.push_back(item);
    return;
  }
  if (IsOptionKeyword(CurrentToken())) {
    item.kind = CrossBodyItemKind::kOption;
    if (ParseItemLevelOption(item.option, state, CovItemLevel::kCross)) {
      cross.body.push_back(item);
      ExpectCoverageItemEnd();
    } else {
      SkipCoverageItemTail();
    }
    return;
  }
  item.kind = CrossBodyItemKind::kBinsSelection;
  if (!ParseBinsSelection(item.bins)) return;
  ReadOtherNamesAsCrossSets(item.bins.select, cross.label, arena_);
  cross.body.push_back(item);
}

bool Parser::ParseBinsSelection(BinsSelection& bins) {
  bins.loc = CurrentLoc();
  if (Check(TokenKind::kKwWildcard)) {
    diag_.Error(Consume().loc,
                "a cross bin is not a wildcard bin; a bins_selection admits "
                "no 'wildcard'",
                Subclause("A.2.11"));
  }
  if (!IsBinsKeyword(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "a cross body item is a bins selection, a coverage option or "
                "a function declaration",
                Subclause("A.2.11"));
    SkipCoverageItemTail();
    return false;
  }
  bins.keyword = BinsKeywordOf(Consume().kind);
  if (Check(TokenKind::kIdentifier)) {
    bins.name = Consume().text;
  } else {
    ReportUnnamedBin(CurrentLoc(), diag_);
  }
  if (Check(TokenKind::kLBracket)) {
    diag_.Error(CurrentLoc(),
                "a cross bin is not an array; a bins_selection subscripts "
                "nothing",
                Subclause("A.2.11"));
    Consume();
    if (!Check(TokenKind::kRBracket)) ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("A.2.11"));
  }
  if (!Match(TokenKind::kEq)) {
    diag_.Error(CurrentLoc(), "expected '=' in bins declaration",
                Subclause("19.5.1"));
    SkipCoverageItemTail();
    return false;
  }
  if (Check(TokenKind::kKwDefault)) {
    diag_.Error(CurrentLoc(),
                "a cross bin selects with a select_expression; 'default' is a "
                "coverpoint bin",
                Subclause("A.2.11"));
    SkipCoverageItemTail();
    return false;
  }
  bins.select = ParseSelectExpression();
  bins.iff = ParseCoverageIffGuard();
  ExpectCoverageItemEnd();
  return true;
}

SelectExpression* Parser::NewSelectExpression(SelectExpressionKind kind,
                                              SourceLoc loc) {
  auto* select = arena_.Create<SelectExpression>();
  select->kind = kind;
  select->loc = loc;
  return select;
}

SelectExpression* Parser::ParseSelectExpression() {
  SelectExpression* lhs = ParseSelectConjunction();
  while (Check(TokenKind::kPipePipe)) {
    auto* joined =
        NewSelectExpression(SelectExpressionKind::kOr, Consume().loc);
    joined->lhs = lhs;
    joined->rhs = ParseSelectConjunction();
    lhs = joined;
  }
  return lhs;
}

SelectExpression* Parser::ParseSelectConjunction() {
  SelectExpression* lhs = ParseSelectPostfix();
  while (Check(TokenKind::kAmpAmp)) {
    auto* joined =
        NewSelectExpression(SelectExpressionKind::kAnd, Consume().loc);
    joined->lhs = lhs;
    joined->rhs = ParseSelectPostfix();
    lhs = joined;
  }
  return lhs;
}

SelectExpression* Parser::ParseSelectPostfix() {
  SelectExpression* operand = ParseSelectPrimary();
  while (Check(TokenKind::kKwWith)) {
    auto* filtered =
        NewSelectExpression(SelectExpressionKind::kWith, Consume().loc);
    filtered->lhs = operand;
    Expect(TokenKind::kLParen, Subclause("A.2.11"));
    filtered->expr = ParseExpr();
    ExpectCoverageCloseParen();
    ParseSelectMatches(*filtered);
    operand = filtered;
  }
  return operand;
}

bool Parser::IdentifierIsCrossName() {
  auto saved = lexer_.SavePos();
  Consume();
  bool ends = Check(TokenKind::kSemicolon) || Check(TokenKind::kKwIff) ||
              Check(TokenKind::kAmpAmp) || Check(TokenKind::kPipePipe) ||
              Check(TokenKind::kRParen) || Check(TokenKind::kKwWith);
  lexer_.RestorePos(saved);
  return ends;
}

SelectExpression* Parser::ParseSelectPrimary() {
  SourceLoc loc = CurrentLoc();
  if (Match(TokenKind::kBang)) {
    if (!Check(TokenKind::kKwBinsof)) {
      diag_.Error(loc,
                  "'!' negates a binsof select_condition; 'binsof' follows it",
                  Subclause("A.2.11"));
    }
    auto* negated = NewSelectExpression(SelectExpressionKind::kNot, loc);
    negated->lhs = ParseSelectPrimary();
    return negated;
  }
  if (Check(TokenKind::kKwBinsof)) return ParseSelectCondition();
  if (Match(TokenKind::kLParen)) {
    auto* grouped =
        NewSelectExpression(SelectExpressionKind::kParenthesized, loc);
    grouped->lhs = ParseSelectExpression();
    ExpectCoverageCloseParen();
    return grouped;
  }
  if (Check(TokenKind::kIdentifier) && IdentifierIsCrossName()) {
    auto* named =
        NewSelectExpression(SelectExpressionKind::kCrossIdentifier, loc);
    named->cross_name = Consume().text;
    return named;
  }
  auto* set = NewSelectExpression(SelectExpressionKind::kCrossSet, loc);
  set->expr = ParseExprBp(kCrossSetExpressionBp);
  ParseSelectMatches(*set);
  return set;
}

SelectExpression* Parser::ParseSelectCondition() {
  auto* condition =
      NewSelectExpression(SelectExpressionKind::kBinsOf, Consume().loc);
  Expect(TokenKind::kLParen, Subclause("A.2.11"));
  if (Check(TokenKind::kIdentifier)) {
    condition->bins_of = Consume().text;
    if (Match(TokenKind::kDot)) {
      condition->bins_of_bin = ExpectIdentifier(Subclause("A.2.11")).text;
    }
  } else {
    diag_.Error(CurrentLoc(),
                "binsof names a coverpoint, a coverpoint's bin or a variable; "
                "none is written",
                Subclause("A.2.11"));
  }
  ExpectCoverageCloseParen();
  if (Match(TokenKind::kKwIntersect)) {
    Expect(TokenKind::kLBrace, Subclause("A.2.11"));
    ParseCovergroupRangeList(condition->intersect);
    Expect(TokenKind::kRBrace, Subclause("A.2.11"));
  }
  return condition;
}

void Parser::ParseSelectMatches(SelectExpression& select) {
  if (!Match(TokenKind::kKwMatches)) return;
  if (Match(TokenKind::kDollar)) {
    select.matches_dollar = true;
    return;
  }
  select.matches = ParseExprBp(kCrossSetExpressionBp);
}

}  // namespace delta
