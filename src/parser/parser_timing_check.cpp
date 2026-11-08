#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"

namespace delta {

TimingCheckKind Parser::ParseTimingCheckKind(std::string_view name) {
  if (name == "$setup") return TimingCheckKind::kSetup;
  if (name == "$hold") return TimingCheckKind::kHold;
  if (name == "$setuphold") return TimingCheckKind::kSetuphold;
  if (name == "$recovery") return TimingCheckKind::kRecovery;
  if (name == "$removal") return TimingCheckKind::kRemoval;
  if (name == "$recrem") return TimingCheckKind::kRecrem;
  if (name == "$width") return TimingCheckKind::kWidth;
  if (name == "$period") return TimingCheckKind::kPeriod;
  if (name == "$skew") return TimingCheckKind::kSkew;
  if (name == "$nochange") return TimingCheckKind::kNochange;
  if (name == "$timeskew") return TimingCheckKind::kTimeskew;
  if (name == "$fullskew") return TimingCheckKind::kFullskew;
  return TimingCheckKind::kSetup;
}

static bool NeedsDataSignal(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kSkew:
    case TimingCheckKind::kNochange:
    case TimingCheckKind::kTimeskew:
    case TimingCheckKind::kFullskew:
      return true;
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
      return false;
  }
  return false;
}

static void ReportBareTripleLimit(DiagEngine& diag, const TimingCheckDecl& tc) {
  const Expr* limit = tc.limits.back();
  if (tc.check_kind == TimingCheckKind::kNochange ||
      limit->kind != ExprKind::kMinTypMax || limit->is_parenthesized) {
    return;
  }
  diag.Error(limit->range.start,
             "a timing check's limit or threshold is an expression, so a "
             "min:typ:max triple there is parenthesized",
             Subclause("A.7.5.2"));
}

bool Parser::CheckNextIsCommaOrRParen() {
  auto saved = lexer_.SavePos();
  Consume();
  bool result = Check(TokenKind::kComma) || Check(TokenKind::kRParen);
  lexer_.RestorePos(saved);
  return result;
}

void Parser::ParseTimingCheckNotifier(TimingCheckDecl& tc) {
  if (Check(TokenKind::kComma)) return;
  if (CheckIdentifier() && CheckNextIsCommaOrRParen()) {
    tc.notifier = Consume().text;
    return;
  }
  diag_.Error(CurrentLoc(),
              "a timing check's notifier is a variable identifier",
              Subclause("A.7.5.2"));
  ParseMinTypMaxExpr();
}

void Parser::ParseTimingCheckTrailingArgs(TimingCheckDecl& tc) {
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kRParen)) break;

    bool two_limit_check = tc.check_kind == TimingCheckKind::kWidth ||
                           tc.check_kind == TimingCheckKind::kSetuphold ||
                           tc.check_kind == TimingCheckKind::kRecrem ||
                           tc.check_kind == TimingCheckKind::kFullskew ||
                           tc.check_kind == TimingCheckKind::kNochange;
    if (two_limit_check && tc.limits.size() < 2) {
      tc.limits.push_back(ParseMinTypMaxExpr());
      ReportBareTripleLimit(diag_, tc);
      continue;
    }

    ParseTimingCheckNotifier(tc);
    ParseExtendedTimingCheckArgs(tc);
    break;
  }
}

void Parser::ParseTimeskewExtendedArgs(TimingCheckDecl& tc) {
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.event_based_flag = ParseExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.remain_active_flag = ParseMinTypMaxExpr();
  }
}

void Parser::ParseOptionalDelayedRef(std::string_view& name, Expr*& expr,
                                     std::string_view production) {
  if (Check(TokenKind::kComma)) return;
  if (!CheckIdentifier()) {
    diag_.Error(CurrentLoc(),
                "a " + std::string(production) + " is a terminal identifier",
                Subclause("A.7.5.2"));
    ParseMinTypMaxExpr();
    return;
  }
  name = Consume().text;
  if (Match(TokenKind::kLBracket)) {
    expr = ParseMinTypMaxExpr();
    Expect(TokenKind::kRBracket, Subclause("31.9"));
  }
}

void Parser::ParseSetupholdExtendedArgs(TimingCheckDecl& tc) {
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timestamp_cond = ParseMinTypMaxExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timecheck_cond = ParseMinTypMaxExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  ParseOptionalDelayedRef(tc.delayed_ref, tc.delayed_ref_expr,
                          "delayed_reference");
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  ParseOptionalDelayedRef(tc.delayed_data, tc.delayed_data_expr,
                          "delayed_data");
}

void Parser::ParseExtendedTimingCheckArgs(TimingCheckDecl& tc) {
  if (tc.check_kind == TimingCheckKind::kTimeskew ||
      tc.check_kind == TimingCheckKind::kFullskew) {
    ParseTimeskewExtendedArgs(tc);
    return;
  }
  if (tc.check_kind == TimingCheckKind::kSetuphold ||
      tc.check_kind == TimingCheckKind::kRecrem) {
    ParseSetupholdExtendedArgs(tc);
  }
}

static void ValidateTimingCheckLimitCount(DiagEngine& diag, SourceLoc loc,
                                          const TimingCheckDecl& tc) {
  if (tc.limits.size() >= 2) return;

  if (tc.check_kind == TimingCheckKind::kSetuphold) {
    diag.Error(loc, "$setuphold requires two timing_check_limit arguments",
               Subclause("31.3.3"));
  } else if (tc.check_kind == TimingCheckKind::kRecrem) {
    diag.Error(loc, "$recrem requires two timing_check_limit arguments",
               Subclause("31.3.6"));
  } else if (tc.check_kind == TimingCheckKind::kFullskew) {
    diag.Error(loc, "$fullskew requires two timing_check_limit arguments",
               Subclause("31.4.3"));
  }
}

static void ValidateTimingCheckEdgeRequired(DiagEngine& diag, SourceLoc loc,
                                            const TimingCheckDecl& tc) {
  if (tc.ref_edge != SpecifyEdge::kNone) return;

  if (tc.check_kind == TimingCheckKind::kWidth) {
    diag.Error(loc, "$width reference_event must be an edge specification",
               Subclause("31.4.4"));
  } else if (tc.check_kind == TimingCheckKind::kPeriod) {
    diag.Error(loc, "$period reference_event must be an edge specification",
               Subclause("31.4.5"));
  }
}

static void ValidateNochangeTimingCheck(DiagEngine& diag, SourceLoc loc,
                                        const TimingCheckDecl& tc) {
  if (tc.check_kind != TimingCheckKind::kNochange) return;

  if (tc.limits.size() < 2) {
    diag.Error(loc,
               "$nochange requires both start_edge_offset and "
               "end_edge_offset arguments",
               Subclause("31.4.6"));
  }
  if (tc.ref_edge != SpecifyEdge::kPosedge &&
      tc.ref_edge != SpecifyEdge::kNegedge) {
    diag.Error(loc,
               "$nochange reference_event must use posedge or negedge "
               "(edge-control specifiers are not allowed)",
               Subclause("31.4.6"));
  }
}

static void ValidateTimingCheckDecl(DiagEngine& diag, SourceLoc loc,
                                    const TimingCheckDecl& tc) {
  ValidateTimingCheckLimitCount(diag, loc, tc);
  ValidateTimingCheckEdgeRequired(diag, loc, tc);
  ValidateNochangeTimingCheck(diag, loc, tc);
}

SpecifyItem* Parser::ParseTimingCheck() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kTimingCheck;
  item->loc = CurrentLoc();
  item->timing_check.loc = item->loc;

  auto name = CurrentToken().text;
  item->timing_check.check_kind = ParseTimingCheckKind(name);
  Consume();

  Expect(TokenKind::kLParen, Subclause("31.2"));

  item->timing_check.ref_edge =
      ParseSpecifyEdge(&item->timing_check.ref_edge_descriptors);
  item->timing_check.ref_terminal = ParseSpecifyTerminal();
  if (Match(TokenKind::kAmpAmpAmp)) {
    item->timing_check.ref_condition = ParseExpr();
  }
  Expect(TokenKind::kComma, Subclause("31.2"));

  bool has_data_signal = NeedsDataSignal(item->timing_check.check_kind);
  if (has_data_signal) {
    item->timing_check.data_edge =
        ParseSpecifyEdge(&item->timing_check.data_edge_descriptors);
    item->timing_check.data_terminal = ParseSpecifyTerminal();
    if (Match(TokenKind::kAmpAmpAmp)) {
      item->timing_check.data_condition = ParseExpr();
    }
    Expect(TokenKind::kComma, Subclause("31.2"));
  }

  if (item->timing_check.check_kind == TimingCheckKind::kSetup) {
    std::swap(item->timing_check.ref_terminal,
              item->timing_check.data_terminal);
    std::swap(item->timing_check.ref_edge, item->timing_check.data_edge);
    std::swap(item->timing_check.ref_edge_descriptors,
              item->timing_check.data_edge_descriptors);
    std::swap(item->timing_check.ref_condition,
              item->timing_check.data_condition);
  }

  item->timing_check.limits.push_back(ParseMinTypMaxExpr());
  ReportBareTripleLimit(diag_, item->timing_check);
  ParseTimingCheckTrailingArgs(item->timing_check);

  ValidateTimingCheckDecl(diag_, item->loc, item->timing_check);
  Expect(TokenKind::kRParen, Subclause("31.2"));
  Expect(TokenKind::kSemicolon, Subclause("31.2"));
  return item;
}

}  // namespace delta
