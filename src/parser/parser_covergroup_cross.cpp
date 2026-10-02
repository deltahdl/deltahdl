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

// The binding power ParseExprBp reads a cross_set_expression at: above the
// `&&` and `||` that join select_expressions (§19.6.1.1), so neither is read
// as an operator of the expression.
constexpr int kCrossSetExpressionBp = 7;

// §19.6 with §19.6.1.4: a cross's name is seen inside its body only as the
// cross itself, so an operand read as a cross_identifier that is not the
// label of the cross `label` -- a queue `q`, or any name in an unlabelled
// cross -- is the cross_set_expression naming that variable.
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

}  // namespace

// A.2.11 covergroup_range_list: covergroup_value_ranges joined by ','.
void Parser::ParseCovergroupRangeList(
    std::vector<CovergroupValueRange>& ranges) {
  do {
    ranges.push_back(ParseCovergroupValueRange());
  } while (Match(TokenKind::kComma));
}

// A.2.11 covergroup_value_range: an expression, `[ lo : hi ]` with either
// bound `$`, `[ center +/- tolerance ]` or `[ center +%- percent ]` (§19.5.1).
CovergroupValueRange Parser::ParseCovergroupValueRange() {
  CovergroupValueRange range;
  if (!Match(TokenKind::kLBracket)) {
    range.lo = ParseExpr();
    return range;
  }
  if (!Match(TokenKind::kDollar)) range.lo = ParseExpr();
  if (Match(TokenKind::kPlusSlashMinus)) {
    range.kind = CovergroupValueRangeKind::kAbsoluteTolerance;
    range.hi = ParseExpr();
  } else if (Match(TokenKind::kPlusPercentMinus)) {
    range.kind = CovergroupValueRangeKind::kRelativeTolerance;
    range.hi = ParseExpr();
  } else {
    range.kind = CovergroupValueRangeKind::kRange;
    Expect(TokenKind::kColon, Subclause("A.2.11"));
    if (!Match(TokenKind::kDollar)) range.hi = ParseExpr();
  }
  Expect(TokenKind::kRBracket, Subclause("A.2.11"));
  return range;
}

// True where the '[' the parse stands on opens a repetition, `[*`, `[->` or
// `[=`, rather than a covergroup_value_range.
bool Parser::AtTransRepetition() {
  if (!Check(TokenKind::kLBracket)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool repetition = Check(TokenKind::kStar) || Check(TokenKind::kArrow) ||
                    Check(TokenKind::kEq);
  lexer_.RestorePos(saved);
  return repetition;
}

// A.2.11 trans_range_list: a trans_item and its repetition, if any (§19.5.2).
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

// A.2.11 trans_list: parenthesized trans_sets joined by ',', each a run of
// trans_range_lists joined by `=>` (§19.5.2).
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

// A.2.11 cover_cross, positioned on the `cross` keyword: its items, its guard
// and its cross_body.
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
  // §19.6 / Syntax 19-4: list_of_cross_items ::= cross_item , cross_item
  // { , cross_item }, where cross_item ::= cover_point_identifier |
  // variable_identifier. The list ends at the optional `iff` guard, the cross
  // body `{`, or the terminating `;`. A cross must name at least two items and
  // each item must be a bare identifier -- expressions may not appear directly
  // in a cross (a coverage point must be defined first).
  SourceLoc start = CurrentLoc();
  bool expr_item = false;
  bool expect_item = true;
  while (!AtEnd()) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kKwIff || k == TokenKind::kLBrace ||
        k == TokenKind::kSemicolon || k == TokenKind::kKwEndgroup) {
      break;
    }
    if (k == TokenKind::kComma) {
      Consume();
      expect_item = true;
      continue;
    }
    if (k == TokenKind::kIdentifier && expect_item) {
      Token name = Consume();
      items.push_back({name.text, name.loc});
      expect_item = false;
      continue;
    }
    // Anything else between items (an operator, a select, a second identifier
    // with no separating comma) means a cross item is a compound expression.
    expr_item = true;
    Consume();
  }
  if (expr_item) {
    diag_.Error(
        start,
        "a cross item shall be a coverage point or variable identifier; "
        "an expression cannot be used directly in a cross",
        Subclause("19.6"));
  } else if (items.size() < 2) {
    diag_.Error(start, "a cross shall list at least two coverage points",
                Subclause("19.6"));
  }
}

// A.2.11 cross_body: `;`, or a brace holding function declarations, options
// and bins selections, each item but a function ending in ';'.
void Parser::ParseCrossBody(CoverCrossDecl& cross, CovergroupBodyState& state) {
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace) &&
         !AtEnd()) {
    Consume();
  }
  if (Match(TokenKind::kSemicolon) || !Match(TokenKind::kLBrace)) return;
  // §19.6.1.3: each cross body holds the implicit typedefs CrossValType and
  // CrossQueueType, which name nothing outside it.
  TypeNameScope cross_types(*this);
  known_types_.insert("CrossValType");
  known_types_.insert("CrossQueueType");
  while (!Check(TokenKind::kRBrace) && !Check(TokenKind::kKwEndgroup) &&
         !AtEnd()) {
    ParseCrossBodyItem(cross, state);
  }
  Expect(TokenKind::kRBrace, Subclause("A.2.11"));
  Match(TokenKind::kSemicolon);
}

// A.2.11 cross_body_item, positioned on its first token: a
// function_declaration, or a bins_selection_or_option with its ';'. The item
// joins the cross's body where it was read whole.
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

// A.2.11 bins_selection: `bins_keyword name = select_expression [ iff ( ... )
// ]`. A bins_selection is no array, takes no `wildcard` and selects with no
// `default`, each of which a coverpoint's bins_or_options admits; each is
// reported where it stands. Returns whether a whole item was read.
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
  if (Check(TokenKind::kIdentifier)) bins.name = Consume().text;
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

// A.2.11 select_expression: `||` binds loosest, then `&&` (§19.6.1.1).
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

// `select_expression with ( with_covergroup_expression ) [ matches ... ]`
// (§19.6.1.2), read onto the operand it follows.
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

// True where the identifier the parse stands on is followed by a token that
// ends a select_expression operand, the shape of a cross_identifier rather
// than of the start of a cross_set_expression.
bool Parser::IdentifierIsCrossName() {
  auto saved = lexer_.SavePos();
  Consume();
  bool ends = Check(TokenKind::kSemicolon) || Check(TokenKind::kKwIff) ||
              Check(TokenKind::kAmpAmp) || Check(TokenKind::kPipePipe) ||
              Check(TokenKind::kRParen) || Check(TokenKind::kKwWith);
  lexer_.RestorePos(saved);
  return ends;
}

// A select_expression operand: `! select_condition`, a select_condition, a
// parenthesized select_expression, a cross_identifier, or a
// cross_set_expression with its `matches` (§19.6.1, §19.6.1.4).
SelectExpression* Parser::ParseSelectPrimary() {
  SourceLoc loc = CurrentLoc();
  if (Match(TokenKind::kBang)) {
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

// A.2.11 select_condition: `binsof ( bins_expression ) [ intersect {
// covergroup_range_list } ]`, bins_expression being a variable or a
// coverpoint with an optional `. bin` (§19.6.1).
SelectExpression* Parser::ParseSelectCondition() {
  auto* condition =
      NewSelectExpression(SelectExpressionKind::kBinsOf, Consume().loc);
  Expect(TokenKind::kLParen, Subclause("A.2.11"));
  if (Check(TokenKind::kIdentifier)) {
    condition->bins_of = Consume().text;
    if (Match(TokenKind::kDot)) {
      condition->bins_of_bin = ExpectIdentifier(Subclause("A.2.11")).text;
    }
  }
  ExpectCoverageCloseParen();
  if (Match(TokenKind::kKwIntersect)) {
    Expect(TokenKind::kLBrace, Subclause("A.2.11"));
    ParseCovergroupRangeList(condition->intersect);
    Expect(TokenKind::kRBrace, Subclause("A.2.11"));
  }
  return condition;
}

// `matches integer_covergroup_expression`, where that expression may be `$`.
void Parser::ParseSelectMatches(SelectExpression& select) {
  if (!Match(TokenKind::kKwMatches)) return;
  if (Match(TokenKind::kDollar)) {
    select.matches_dollar = true;
    return;
  }
  select.matches = ParseExprBp(kCrossSetExpressionBp);
}

}  // namespace delta
