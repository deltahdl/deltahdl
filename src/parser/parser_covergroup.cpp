#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/covergroup_sample_formal_uses.h"
#include "parser/parser.h"
#include "parser/parser_covergroup_internal.h"

namespace delta {

namespace {

bool IsCoverpointOrCross(TokenKind k) {
  return k == TokenKind::kKwCoverpoint || k == TokenKind::kKwCross;
}

bool InstanceOptionForbiddenAtItemLevel(std::string_view member, bool cross) {
  if (member == "name" || member == "per_instance" ||
      member == "get_inst_coverage") {
    return true;
  }
  if (!cross) {
    return member == "cross_num_print_missing" ||
           member == "cross_retain_auto_bins";
  }
  return member == "auto_bin_max" || member == "detect_overlap";
}

bool TypeOptionForbiddenAtItemLevel(std::string_view member, bool cross) {
  if (member == "strobe" || member == "merge_instances" ||
      member == "distribute_first") {
    return true;
  }
  return cross && member == "real_interval";
}

bool IsLiteralOne(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kIntegerLiteral &&
         e->int_val == 1;
}

bool IsLengthZeroTransition(const TransSet& set) {
  if (set.steps.size() != 1 || set.steps[0].items.size() != 1) return false;
  const TransRangeList& step = set.steps[0];
  if (step.repetition == TransRepetition::kNone) return true;
  return step.repetition == TransRepetition::kConsecutive &&
         IsLiteralOne(step.repeat_lo) &&
         (step.repeat_hi == nullptr || IsLiteralOne(step.repeat_hi));
}

bool HasUnboundedStep(const TransSet& set) {
  for (const TransRangeList& step : set.steps) {
    if (step.repetition == TransRepetition::kGoto ||
        step.repetition == TransRepetition::kNonconsecutive) {
      return true;
    }
  }
  return false;
}

void ReportUnboundedExcludingTransitions(const BinsOrOptions& bins,
                                         DiagEngine& diag) {
  bool ignore = bins.keyword == BinsKeyword::kIgnoreBins;
  for (const TransSet& set : bins.transitions) {
    if (!HasUnboundedStep(set)) continue;
    diag.Error(set.loc,
               std::format("an {} transition cannot be of unbounded or "
                           "undetermined length",
                           ignore ? "ignore_bins" : "illegal_bins"),
               Subclause(ignore ? "19.5.5" : "19.5.6"));
  }
}

bool IsClockingEventName(const Expr* e, bool prefix) {
  if (e->kind == ExprKind::kIdentifier) return true;
  if (e->kind == ExprKind::kMemberAccess) {
    return IsClockingEventName(e->lhs, true);
  }
  return e->kind == ExprKind::kSelect && prefix;
}

}  // namespace

void ReportStrayCoverageToken(const Token& stray, DiagEngine& diag) {
  if (stray.Is(TokenKind::kEof)) return;
  diag.Error(stray.loc,
             std::format("a covergroup item is complete here; '{}' is not "
                         "part of it",
                         stray.text),
             Subclause("A.2.11"));
}

void ReportUnnamedBin(SourceLoc at, DiagEngine& diag) {
  diag.Error(at, "a bin is named; a bin_identifier follows its bins keyword",
             Subclause("A.2.11"));
}

void Parser::ParseCovergroupDecl(std::vector<ModuleItem*>& items) {
  auto* item = arena_.Create<ModuleItem>();
  auto* cg = arena_.Create<CovergroupDecl>();
  item->kind = ModuleItemKind::kCovergroupDecl;
  item->loc = CurrentLoc();
  item->covergroup = cg;
  Expect(TokenKind::kKwCovergroup, Subclause("19.3"));

  if (Check(TokenKind::kKwExtends)) {
    Consume();
    auto base = Expect(TokenKind::kIdentifier, Subclause("19.4.1"));
    item->name = base.text;
    item->covergroup_extends_base = base.text;
    cg->extends_base = base.text;
    RejectDerivedCovergroupTail();
  } else {
    item->name = Expect(TokenKind::kIdentifier, Subclause("19.3")).text;
    RejectNamedCovergroupExtends();
  }
  cg->name = item->name;
  known_types_.insert(item->name);

  CovergroupBodyState state;
  state.cg = cg;
  if (Check(TokenKind::kLParen)) ParseCovergroupFormals(state);
  ParseCoverageEvent(state);
  Expect(TokenKind::kSemicolon, Subclause("19.3"));

  while (!Check(TokenKind::kKwEndgroup) && !AtEnd()) {
    ParseCovergroupItem(state);
  }
  Expect(TokenKind::kKwEndgroup, Subclause("19.3"));
  ReportSampleFormalsOutsideCoverpoints(*cg, diag_);
  MatchEndLabel(item->name);
  items.push_back(item);
}

void Parser::RejectDerivedCovergroupTail() {
  if (Check(TokenKind::kLParen) || Check(TokenKind::kAt) ||
      Check(TokenKind::kAtAt) || Check(TokenKind::kKwWith)) {
    diag_.Error(CurrentLoc(),
                "a covergroup that extends a base declares no port list and no "
                "coverage event; it inherits the base's",
                Subclause("A.2.11"));
  }
}

void Parser::RejectNamedCovergroupExtends() {
  if (!Check(TokenKind::kKwExtends)) return;
  diag_.Error(CurrentLoc(),
              "a covergroup that declares its own name cannot also extend a "
              "base; a derived covergroup is written 'covergroup extends "
              "base;'",
              Subclause("A.2.11"));
  Consume();
  ExpectIdentifier(Subclause("19.4.1"));
}

void Parser::ParseCoverageFormalList(std::vector<FunctionArg>& args,
                                     std::string_view output_message,
                                     Subclause subclause) {
  Expect(TokenKind::kLParen, Subclause("19.3"));
  if (Match(TokenKind::kRParen)) return;
  FuncArgScan scan;
  do {
    if (Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInout)) {
      diag_.Error(CurrentLoc(), std::string(output_message), subclause);
    }
    ParseOneFunctionArg(args, scan, true);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen, Subclause("19.3"));
}

void Parser::ParseCovergroupFormals(CovergroupBodyState& state) {
  ParseCoverageFormalList(state.cg->formals,
                          "a covergroup formal argument cannot be declared "
                          "'output' or 'inout'",
                          Subclause("19.3"));
  for (const FunctionArg& formal : state.cg->formals) {
    state.formals.push_back(formal.name);
  }
}

void Parser::ParseCoverageEvent(CovergroupBodyState& state) {
  CoverageEvent& event = state.cg->event;
  if (Match(TokenKind::kAt)) {
    event.kind = CoverageEventKind::kClocking;
    if (Check(TokenKind::kIdentifier) || Check(TokenKind::kSystemIdentifier)) {
      EventExpr named;
      named.signal = ParseExpr();
      if (!IsClockingEventName(named.signal, false)) {
        diag_.Error(named.signal->range.start,
                    "an unparenthesized clocking event is '@' and a name; an "
                    "expression is parenthesized",
                    Subclause("A.6.5"));
      }
      event.clocking.push_back(named);
      return;
    }
    Expect(TokenKind::kLParen, Subclause("19.3"));
    event.clocking = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("19.3"));
  } else if (Match(TokenKind::kAtAt)) {
    event.kind = CoverageEventKind::kBlockEvent;
    Expect(TokenKind::kLParen, Subclause("19.3"));
    ParseBlockEventExpression(event.block_event);
    Expect(TokenKind::kRParen, Subclause("19.3"));
  } else if (Match(TokenKind::kKwWith)) {
    event.kind = CoverageEventKind::kSampleFunction;
    ParseSampleFunctionEvent(state);
  }
}

void Parser::ParseSampleFunctionEvent(CovergroupBodyState& state) {
  Expect(TokenKind::kKwFunction, Subclause("19.8.1"));
  auto sample_id = ExpectIdentifier(Subclause("19.8.1"));
  if (sample_id.text != "sample") {
    diag_.Error(sample_id.loc,
                "expected 'sample', got '" + std::string(sample_id.text) + "'",
                Subclause("19.3"));
  }
  SourceLoc formals_loc = CurrentLoc();
  std::vector<FunctionArg>& formals = state.cg->event.sample_formals;
  ParseCoverageFormalList(formals,
                          "a sample method formal argument cannot designate "
                          "an output direction",
                          Subclause("19.8.1"));
  for (const FunctionArg& formal : formals) {
    for (std::string_view taken : state.formals) {
      if (taken != formal.name) continue;
      diag_.Error(formals_loc,
                  "sample method formal argument '" + std::string(formal.name) +
                      "' shares the covergroup argument scope and cannot "
                      "reuse a covergroup formal-argument name",
                  Subclause("19.8.1"));
    }
  }
}

void Parser::ParseBlockEventExpression(std::vector<BlockEventTerm>& terms) {
  do {
    if (!Check(TokenKind::kKwBegin) && !Check(TokenKind::kKwEnd)) {
      diag_.Error(CurrentLoc(), "expected 'begin' or 'end' in block event",
                  Subclause("19.3"));
      return;
    }
    BlockEventTerm term;
    term.is_begin = Consume().Is(TokenKind::kKwBegin);
    ParseHierarchicalBtfIdentifier(term.path);
    terms.push_back(term);
  } while (Match(TokenKind::kKwOr));
}

void Parser::ParseHierarchicalBtfIdentifier(
    std::vector<std::string_view>& path) {
  if (Check(TokenKind::kSystemIdentifier) && CurrentToken().text == "$root") {
    path.push_back(Consume().text);
    Expect(TokenKind::kDot, Subclause("A.2.11"));
  }
  path.push_back(ExpectIdentifier(Subclause("A.2.11")).text);
  while (true) {
    if (Match(TokenKind::kLBracket)) {
      ParseExpr();
      Expect(TokenKind::kRBracket, Subclause("A.2.11"));
    } else if (Match(TokenKind::kDot) || Match(TokenKind::kColonColon)) {
      path.push_back(ExpectIdentifier(Subclause("A.2.11")).text);
    } else if (Match(TokenKind::kHash)) {
      std::vector<std::pair<std::string_view, Expr*>> params;
      ParseParamValueAssignment(params);
    } else {
      return;
    }
  }
}

void Parser::ParseCovergroupItem(CovergroupBodyState& state) {
  ParseAttributes();
  if (IsOptionKeyword(CurrentToken())) {
    ParseCovergroupOption(state);
    return;
  }
  if (Check(TokenKind::kKwCross)) {
    ParseCoverCross(state, {}, {});
    return;
  }
  if (Check(TokenKind::kKwCoverpoint)) {
    ParseCoverPoint(state, {}, {}, nullptr);
    return;
  }
  if (Check(TokenKind::kIdentifier) && IdentifierOpensCoverageLabel()) {
    ParseLabelledCoverageSpec(state, nullptr);
    return;
  }
  if (AtDataTypeOrVoid()) {
    DataType data_type = ParseCoverpointDataType();
    ParseLabelledCoverageSpec(state, &data_type);
    return;
  }
  RejectCovergroupItem();
}

void Parser::ParseLabelledCoverageSpec(CovergroupBodyState& state,
                                       const DataType* data_type) {
  Token label = Consume();
  if (Match(TokenKind::kColon) && IsCoverpointOrCross(CurrentToken().kind)) {
    if (Check(TokenKind::kKwCross)) {
      if (data_type != nullptr) {
        diag_.Error(label.loc,
                    "a cross takes no data type; one is written before a "
                    "coverpoint's label alone",
                    Subclause("A.2.11"));
      }
      ParseCoverCross(state, label.text, label.loc);
    } else {
      ParseCoverPoint(state, label.text, label.loc, data_type);
    }
    return;
  }
  RejectCovergroupItem();
}

void Parser::RejectCovergroupItem() {
  diag_.Error(CurrentLoc(),
              "a covergroup item is a coverpoint, a cross or a coverage "
              "option",
              Subclause("A.2.11"));
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndgroup) &&
         !AtEnd()) {
    Consume();
  }
  Match(TokenKind::kSemicolon);
}

bool Parser::ParseCoverageOption(CoverageOption& option) {
  Token keyword = Consume();
  option.is_type_option = keyword.text == "type_option";
  auto report = [&](SourceLoc loc) {
    diag_.Error(loc,
                "a coverage option is set as '" + std::string(keyword.text) +
                    ".member = value'",
                Subclause("A.2.11"));
  };
  if (!Match(TokenKind::kDot)) {
    report(CurrentLoc());
    return false;
  }
  if (!Check(TokenKind::kIdentifier)) {
    report(CurrentLoc());
    return false;
  }
  Token member = Consume();
  option.member = member.text;
  option.loc = member.loc;
  if (!Match(TokenKind::kEq)) {
    report(CurrentLoc());
    return true;
  }
  option.value = ParseExpr();
  return true;
}

void Parser::RejectFormalInTypeOption(const CoverageOption& option,
                                      const CovergroupBodyState& state) {
  if (!option.is_type_option) return;
  const Expr* formal = FindNamedIdentifier(option.value, state.formals);
  if (formal == nullptr) return;
  diag_.Error(formal->range.start,
              "a type option is set with a constant expression; covergroup "
              "formal '" +
                  std::string(formal->text) + "' is not one",
              Subclause("19.7.1"));
}

void Parser::ParseCovergroupOption(CovergroupBodyState& state) {
  CoverageSpecOrOption item;
  item.kind = CoverageSpecKind::kOption;
  std::string keyword(CurrentToken().text);
  if (ParseCoverageOption(item.option)) {
    std::string option_name = keyword + '.' + std::string(item.option.member);
    if (!state.seen_options.insert(option_name).second) {
      diag_.Error(item.option.loc,
                  "coverage option '" + option_name +
                      "' is assigned more than once in the same covergroup "
                      "definition",
                  Subclause("19.7"));
    }
    RejectFormalInTypeOption(item.option, state);
    state.cg->items.push_back(item);
  }
  if (item.option.value != nullptr && !Check(TokenKind::kSemicolon)) {
    ReportStrayCoverageToken(CurrentToken(), diag_);
  }
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndgroup) &&
         !AtEnd()) {
    Consume();
  }
  Match(TokenKind::kSemicolon);
}

bool Parser::ParseItemLevelOption(CoverageOption& option,
                                  const CovergroupBodyState& state,
                                  CovItemLevel level) {
  if (!ParseCoverageOption(option)) return false;
  const bool kCross = level == CovItemLevel::kCross;
  const bool kForbidden =
      option.is_type_option
          ? TypeOptionForbiddenAtItemLevel(option.member, kCross)
          : InstanceOptionForbiddenAtItemLevel(option.member, kCross);
  if (kForbidden) {
    diag_.Error(
        option.loc,
        "coverage option '" +
            std::string(option.is_type_option ? "type_option." : "option.") +
            std::string(option.member) + "' may not be specified at the " +
            std::string(kCross ? "cross" : "coverpoint") + " level",
        Subclause(option.is_type_option ? "19.7.1" : "19.7"));
  }
  RejectFormalInTypeOption(option, state);
  return option.value != nullptr;
}

void Parser::TakeCoverageName(CovergroupBodyState& state, std::string_view name,
                              SourceLoc loc) {
  if (name.empty() || state.names.insert(name).second) return;
  diag_.Error(loc,
              "the name '" + std::string(name) +
                  "' already names a coverpoint or cross of covergroup '" +
                  std::string(state.cg->name) + "'",
              Subclause("19.5"));
}

bool Parser::IdentifierOpensCoverageLabel() {
  auto saved = lexer_.SavePos();
  Consume();
  bool labelled = Check(TokenKind::kColon);
  lexer_.RestorePos(saved);
  return labelled;
}

bool Parser::IdentifierOpensCoverPointWith() {
  auto saved = lexer_.SavePos();
  Consume();
  bool with = Check(TokenKind::kKwWith);
  lexer_.RestorePos(saved);
  return with;
}

DataType Parser::ParseCoverpointDataType() {
  DataType dtype = ParseDataType();
  if (Check(TokenKind::kLBracket)) ParsePackedDims(dtype);
  return dtype;
}

bool Parser::BraceOpensCoverpointBody() {
  auto saved = lexer_.SavePos();
  Consume();
  Token t = CurrentToken();
  bool is_body = t.Is(TokenKind::kRBrace) || IsBinsKeyword(t.kind) ||
                 t.Is(TokenKind::kKwWildcard) || t.Is(TokenKind::kAttrStart) ||
                 IsOptionKeyword(t);
  lexer_.RestorePos(saved);
  return is_body;
}

Expr* Parser::ParseCoverpointHead() {
  if (Check(TokenKind::kSemicolon) || Check(TokenKind::kKwIff) ||
      Check(TokenKind::kKwEndgroup) || AtEnd() ||
      (Check(TokenKind::kLBrace) && BraceOpensCoverpointBody())) {
    diag_.Error(CurrentLoc(),
                "a coverpoint covers an expression; none is written",
                Subclause("A.2.11"));
    return nullptr;
  }
  return ParseExpr();
}

Expr* Parser::ParseCoverageIffGuard() {
  if (!Match(TokenKind::kKwIff)) return nullptr;
  if (Match(TokenKind::kLParen)) {
    Expr* guard = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("A.2.11"));
    return guard;
  }
  diag_.Error(CurrentLoc(),
              "a coverage guard is written 'iff ( expression )'; its "
              "expression is parenthesized",
              Subclause("A.2.11"));
  if (Check(TokenKind::kSemicolon) || Check(TokenKind::kLBrace)) return nullptr;
  return ParseExpr();
}

void Parser::ParseCoverPoint(CovergroupBodyState& state, std::string_view label,
                             SourceLoc label_loc, const DataType* data_type) {
  auto* cp = arena_.Create<CoverPointDecl>();
  cp->loc = label.empty() ? CurrentLoc() : label_loc;
  cp->label = label;
  if (data_type != nullptr) {
    cp->has_data_type = true;
    cp->data_type = *data_type;
  }
  Consume();
  cp->expr = ParseCoverpointHead();
  cp->iff = ParseCoverageIffGuard();
  if (!label.empty()) {
    TakeCoverageName(state, label, label_loc);
  } else if (cp->expr != nullptr && cp->expr->kind == ExprKind::kIdentifier) {
    TakeCoverageName(state, cp->expr->text, cp->expr->range.start);
  }
  CoverageSpecOrOption item;
  item.kind = CoverageSpecKind::kCoverPoint;
  item.cover_point = cp;
  state.cg->items.push_back(item);
  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace)) {
    ReportStrayCoverageToken(CurrentToken(), diag_);
  }
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kLBrace) &&
         !AtEnd()) {
    Consume();
  }
  if (Match(TokenKind::kSemicolon) || !Match(TokenKind::kLBrace)) return;
  while (!Check(TokenKind::kRBrace) && !Check(TokenKind::kKwEndgroup) &&
         !AtEnd()) {
    ParseAttributes();
    BinsOrOptions bins;
    if (ParseBinsOrOptions(bins, state)) cp->bins.push_back(bins);
  }
  Expect(TokenKind::kRBrace, Subclause("A.2.11"));
}

bool Parser::OpensCoverageBodyItem() {
  const Token& t = CurrentToken();
  return t.Is(TokenKind::kRBrace) || IsBinsKeyword(t.kind) ||
         t.Is(TokenKind::kKwWildcard) || t.Is(TokenKind::kAttrStart) ||
         t.Is(TokenKind::kKwFunction) || IsOptionKeyword(t);
}

void Parser::SkipCoverageItemTail() {
  int depth = 0;
  while (!AtEnd() && !Check(TokenKind::kKwEndgroup)) {
    if (depth == 0 && Check(TokenKind::kSemicolon)) {
      Consume();
      return;
    }
    if (depth == 0 && Check(TokenKind::kRBrace)) return;
    if (Check(TokenKind::kLBrace) || Check(TokenKind::kApostropheLBrace) ||
        Check(TokenKind::kLParen) || Check(TokenKind::kLBracket)) {
      ++depth;
    } else if (depth > 0 &&
               (Check(TokenKind::kRBrace) || Check(TokenKind::kRParen) ||
                Check(TokenKind::kRBracket))) {
      --depth;
    }
    Consume();
  }
}

void Parser::ExpectCoverageItemEnd() {
  if (Match(TokenKind::kSemicolon)) return;
  diag_.Error(CurrentLoc(), "missing ';' in covergroup item",
              Subclause("19.3"));
  if (!OpensCoverageBodyItem()) SkipCoverageItemTail();
}

void Parser::ExpectCoverageCloseParen() {
  if (Match(TokenKind::kRParen)) return;
  diag_.Error(CurrentLoc(), "missing ')' in covergroup item",
              Subclause("19.3"));
}

bool Parser::ParseBinsOrOptions(BinsOrOptions& bins,
                                CovergroupBodyState& state) {
  bins.loc = CurrentLoc();
  if (IsOptionKeyword(CurrentToken())) {
    bins.kind = BinsOrOptionsKind::kOption;
    if (!ParseItemLevelOption(bins.option, state, CovItemLevel::kCoverpoint)) {
      SkipCoverageItemTail();
      return false;
    }
    ExpectCoverageItemEnd();
    return true;
  }
  SourceLoc wildcard_loc;
  if (Check(TokenKind::kKwWildcard)) {
    wildcard_loc = Consume().loc;
    bins.wildcard = true;
  }
  if (!IsBinsKeyword(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "a coverpoint body item is a bins declaration or a coverage "
                "option",
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
  if (Match(TokenKind::kLBracket)) {
    bins.is_array = true;
    if (!Check(TokenKind::kRBracket)) bins.array_size = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("A.2.11"));
  }
  if (!Match(TokenKind::kEq)) {
    diag_.Error(CurrentLoc(), "expected '=' in bins declaration",
                Subclause("19.5.1"));
    SkipCoverageItemTail();
    return false;
  }
  if (Check(TokenKind::kKwDefault) && bins.wildcard) {
    diag_.Error(wildcard_loc,
                "'wildcard' qualifies a bin over values or transitions; a "
                "'default' bin takes none",
                Subclause("A.2.11"));
  }
  ParseBinsValue(bins);
  bins.iff = ParseCoverageIffGuard();
  ExpectCoverageItemEnd();
  return true;
}

void Parser::ParseBinsValue(BinsOrOptions& bins) {
  if (Match(TokenKind::kKwDefault)) {
    bins.kind = BinsOrOptionsKind::kDefault;
    if (Check(TokenKind::kKwSequence)) {
      if (bins.is_array) {
        diag_.Error(CurrentLoc(), "a 'default sequence' bin is not an array",
                    Subclause("A.2.11"));
      }
      Consume();
      bins.kind = BinsOrOptionsKind::kDefaultSequence;
    }
    return;
  }
  if (Check(TokenKind::kLParen)) {
    if (bins.array_size != nullptr) {
      diag_.Error(CurrentLoc(),
                  "a transition bin's array is written '[ ]'; its size is the "
                  "number of transitions",
                  Subclause("A.2.11"));
    }
    bins.kind = BinsOrOptionsKind::kTransitions;
    ParseTransList(bins.transitions);
    CheckTransitionBins(bins);
    return;
  }
  if (Match(TokenKind::kLBrace)) {
    bins.kind = BinsOrOptionsKind::kValues;
    ParseCovergroupRangeList(bins.ranges);
    Expect(TokenKind::kRBrace, Subclause("A.2.11"));
    if (Match(TokenKind::kKwWith)) {
      Expect(TokenKind::kLParen, Subclause("A.2.11"));
      bins.with_expr = ParseExpr();
      ExpectCoverageCloseParen();
    }
    return;
  }
  if (Check(TokenKind::kIdentifier) && IdentifierOpensCoverPointWith()) {
    bins.kind = BinsOrOptionsKind::kCoverPointWith;
    bins.with_cover_point = Consume().text;
    Consume();
    Expect(TokenKind::kLParen, Subclause("A.2.11"));
    bins.with_expr = ParseExpr();
    ExpectCoverageCloseParen();
    return;
  }
  bins.kind = BinsOrOptionsKind::kSetExpression;
  bins.set_expr = ParseExpr();
}

void Parser::CheckTransitionBins(const BinsOrOptions& bins) {
  for (const TransSet& set : bins.transitions) {
    if (IsLengthZeroTransition(set)) {
      diag_.Error(set.loc,
                  "a transition of length 0 is illegal; its trans_set covers "
                  "a single value range",
                  Subclause("19.5.2"));
    }
  }
  if (bins.keyword != BinsKeyword::kBins) {
    ReportUnboundedExcludingTransitions(bins, diag_);
    return;
  }
  if (!bins.is_array || bins.array_size != nullptr) return;
  for (const TransSet& set : bins.transitions) {
    if (!HasUnboundedStep(set)) continue;
    diag_.Error(set.loc,
                "a transition bin array '[ ]' cannot hold a transition of "
                "unbounded length",
                Subclause("19.5.2"));
    return;
  }
}

}  // namespace delta
