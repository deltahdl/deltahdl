// The system timing checks of IEEE 1800-2023 §31 as A.7.5 writes them: the
// twelve commands of A.7.5.1, read by Parser::ParseTimingCheck, and the
// arguments A.7.5.2 gives them, with the checks of their counts and edges a
// parse can make. Parser::ParseSpecifyItem in parser_specify.cpp hands a
// timing check here, and the events' edges and terminals are read by the
// readers that file shares with the module path declarations.

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

// A.7.5.2 writes a timing_check_limit as an expression and $width's threshold
// as a constant_expression, neither of them a mintypmax_expression, so a
// min:typ:max triple standing as either is parenthesized; $nochange's two
// offsets, which share TimingCheckDecl::limits with them, are
// mintypmax_expressions and take one bare. ParseMinTypMaxExpr reads a triple
// either way and marks the parenthesized one, so the last limit `tc` read is
// reported here when it is a bare triple.
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

// A.7.5.2's notifier, `variable_identifier`, at the place every A.7.5.1
// production gives it, after the check's limits: an identifier, simple or
// escaped, that the ',' or ')' ending the argument follows. The notifier is
// optional inside its brackets, `[ , [ notifier ] ... ]`, so a ',' standing
// where it would is an omitted notifier and is left for the arguments behind
// it. Anything else there is reported and read as an expression, so that the
// rest of the list is still read.
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

    // Some checks still expect a second timing_check_limit at this position
    // ($width's threshold; the mandatory pair of $setuphold/$recrem/$fullskew;
    // $nochange's start/end edge offsets). Whatever stands there is that
    // limit, a specparam-named constant included, and not the notifier.
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

    // With the limits read, what follows is the notifier, given or omitted,
    // and then the arguments the check's own production writes behind it.
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

// A.7.5.2's delayed_reference and delayed_data, each `terminal_identifier |
// terminal_identifier [ constant_mintypmax_expression ]`, at the place
// $setuphold's and $recrem's productions give them, where `production` names
// which. Each is optional inside its brackets, so a ',' standing where it
// would is an omitted one and is left for what follows. What else stands
// there is reported and read as an expression, so that the rest of the list
// is still read.
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

// A.7.5.1 writes arguments past the notifier for four checks alone:
// $setuphold and $recrem take `[ , [ timestamp_condition ] [ , [
// timecheck_condition ] [ , [ delayed_reference ] [ , [ delayed_data ] ] ] ]`,
// and $timeskew and $fullskew take `[ , [ event_based_flag ] [ , [
// remain_active_flag ] ]`. The eight others end at `[ , [ notifier ] ] )`, so
// a ',' after their notifier is left standing where Parser::ParseTimingCheck
// expects the ')' and reports it under §31.2.
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

// Checks that timing checks requiring two timing_check_limit arguments
// ($setuphold, $recrem, $fullskew) actually received them.
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

// Checks that $width and $period reference events carry an edge specification.
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

// Checks the $nochange-specific argument-count and edge-kind requirements.
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
  // The check's own first token, which is the keyword §31.2's Syntax 31-1 opens
  // every system_timing_check production with. TimingCheckDecl::loc
  // (parser/ast_specify.h) is what carries it past the parse:
  // BuildTimingCheckUnderOptions (simulator/specify_timing_check.cpp) copies it
  // into TimingCheckEntry::loc, and that is where a §31 violation is reported.
  // A reader given the specify block's own position instead would be sent to
  // the block and left to guess which of its checks fired.
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

  // §31.3.1 is the one check of Clause 31 that names its data event first.
  // Syntax 31-3 writes `$setup(data_event, reference_event, ...)` where Syntax
  // 31-4, 31-5, 31-6, 31-7 and 31-8 write the reference event first, and Tables
  // 31-1 through 31-6 say the same. The two terminals are read positionally
  // above, so without this a $setup arrives with each in the field named for
  // the other, and everything downstream -- BuildTimingCheckUnderOptions,
  // SdfAnnotationMatchesCheck and the §31.3 verdicts -- reads them by name.
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
