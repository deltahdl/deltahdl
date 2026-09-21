#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

// CPD-dedup helpers for the statements this file parses. The begin/fork block
// name is not among them: it is Parser::MatchEndBlockLabel in
// src/parser/parser_stmt_block.cpp, beside the two statements that ask for it
// and shared with the generate block in src/parser/parser_generate.cpp.
struct ParserStmtHelpers {
  static void ApplyStmtLabel(Parser& p, Stmt* stmt,
                             std::string_view prefix_label) {
    if (!prefix_label.empty() && stmt->label.empty()) {
      stmt->label = prefix_label;
    } else if (!prefix_label.empty() && !stmt->label.empty()) {
      p.diag_.Error(stmt->range.start,
                    "cannot have both a statement label and a block name",
                    Subclause("9.3.5"));
    }
  }

  static void CheckQualifiedElseIfBranches(Parser& p, Stmt* stmt) {
    for (Stmt* cur = stmt->else_branch; cur && cur->kind == StmtKind::kIf;
         cur = cur->else_branch) {
      if (cur->qualifier != CaseQualifier::kNone) {
        p.diag_.Error(cur->range.start,
                      "unique, unique0, or priority cannot appear on an "
                      "else-if branch; wrap the nested if in begin-end",
                      Subclause("12.4.2"));
        break;
      }
    }
  }

  static void ApplyStmtQualifierAndAttrs(Parser& p, Stmt* stmt,
                                         CaseQualifier qual,
                                         std::vector<Attribute>& attrs) {
    if (!attrs.empty()) stmt->attrs = std::move(attrs);
    if (qual != CaseQualifier::kNone) stmt->qualifier = qual;
    if (qual != CaseQualifier::kNone && stmt->kind == StmtKind::kIf) {
      CheckQualifiedElseIfBranches(p, stmt);
    }
  }

  // One item of A.6.8's for_initialization, which is a list_of_variable_
  // assignments, each `variable_lvalue = expression`, or for_variable_
  // declarations, each `[ var ] data_type variable_identifier = expression
  // { , variable_identifier = expression }`: every item assigns with '='.
  // Parser::ParseAssignmentOrExprNoSemi reads that as a
  // StmtKind::kBlockingAssign, and reads the bare `i` or the `i <= 0` neither
  // form admits as an expression statement or a nonblocking assignment, which
  // is reported at the item and kept as read.
  static Stmt* ParseForInitItem(Parser& p, const char* form) {
    SourceLoc loc = p.CurrentLoc();
    Stmt* init = p.ParseAssignmentOrExprNoSemi();
    if (init->kind != StmtKind::kBlockingAssign) {
      p.diag_.Error(loc, form, Subclause("A.6.8"));
    }
    return init;
  }

  static void ParseForLocalDeclInits(Parser& p, Stmt* stmt) {
    do {
      p.Match(TokenKind::kKwVar);
      stmt->for_init_types.push_back(p.ParseDataType());
      stmt->for_inits.push_back(ParseForInitItem(
          p,
          "a for loop's variable declaration is written 'data_type "
          "variable_identifier = expression'; the initial value is not "
          "optional"));
    } while (p.Match(TokenKind::kComma));
    p.Expect(TokenKind::kSemicolon, Subclause("12.7.1"));
  }

  static void ParseForPlainInits(Parser& p, Stmt* stmt) {
    do {
      if (p.Check(TokenKind::kKwVar) ||
          IsDataTypeKeyword(p.CurrentToken().kind)) {
        // The first control variable was a plain assignment, so a later item
        // attempting a local declaration mixes declared and non-declared
        // control variables, which is not allowed.
        p.diag_.Error(
            p.CurrentLoc(),
            "for-loop initialization shall declare either all or none "
            "of its control variables locally",
            Subclause("12.7.1"));
        p.Match(TokenKind::kKwVar);
        stmt->for_init_types.push_back(p.ParseDataType());
      } else {
        stmt->for_init_types.emplace_back();
      }
      stmt->for_inits.push_back(ParseForInitItem(
          p,
          "a for loop's initialization is a list of variable assignments, "
          "each 'variable_lvalue = expression', or of variable "
          "declarations"));
    } while (p.Match(TokenKind::kComma));
    p.Expect(TokenKind::kSemicolon, Subclause("12.7.1"));
  }

  // Whether a statement read from a for loop's third header position has one
  // of the three forms A.6.8 gives for_step_assignment: an
  // operator_assignment, which Parser::ParseAssignmentOrExprNoSemi records as
  // a StmtKind::kBlockingAssign for every assignment_operator; an
  // inc_or_dec_expression; or a function_subroutine_call. A nonblocking
  // assignment and a bare expression are neither.
  static bool IsForStepAssignment(const Stmt* step) {
    if (step->kind == StmtKind::kBlockingAssign) return true;
    if (step->kind != StmtKind::kExprStmt || step->expr == nullptr) {
      return false;
    }
    const Expr* e = step->expr;
    if (e->kind == ExprKind::kCall || e->kind == ExprKind::kSystemCall) {
      return true;
    }
    return (e->kind == ExprKind::kUnary ||
            e->kind == ExprKind::kPostfixUnary) &&
           (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
  }

  static Stmt* ParseForStep(Parser& p) {
    SourceLoc loc = p.CurrentLoc();
    Stmt* step = p.ParseAssignmentOrExprNoSemi();
    if (!IsForStepAssignment(step)) {
      p.diag_.Error(loc,
                    "a for loop's step is an operator assignment, an "
                    "increment or decrement, or a subroutine call",
                    Subclause("A.6.8"));
    }
    return step;
  }
};

static CaseQualifier TokenToCaseQualifier(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwUnique:
      return CaseQualifier::kUnique;
    case TokenKind::kKwUnique0:
      return CaseQualifier::kUnique0;
    case TokenKind::kKwPriority:
      return CaseQualifier::kPriority;
    default:
      return CaseQualifier::kNone;
  }
}

Stmt* Parser::ParseStmt() {
  auto prefix_label = TryParseStmtLabel();
  auto attrs = ParseAttributes();

  if (Match(TokenKind::kSemicolon)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kNull;
    stmt->label = prefix_label;
    stmt->attrs = std::move(attrs);
    return stmt;
  }

  auto qual = TokenToCaseQualifier(CurrentToken().kind);
  if (qual != CaseQualifier::kNone) {
    Consume();
  }

  Stmt* stmt = ParseStmtBody(prefix_label);
  if (stmt != nullptr) {
    ParserStmtHelpers::ApplyStmtLabel(*this, stmt, prefix_label);
    ParserStmtHelpers::ApplyStmtQualifierAndAttrs(*this, stmt, qual, attrs);
  }
  return stmt;
}

Stmt* Parser::ParseStmtBody(std::string_view prefix_label) {
  // §14.7: a clocking block is a declaration inside a module, interface,
  // checker or program, never a statement, so one standing where a statement
  // belongs is rejected before the switch rather than read as an expression.
  // The three positions the sentence names are the ones that reach here.
  if (AtClockingDecl()) {
    RejectClockingDecl(
        "a clocking block shall not be declared inside a function, task, or "
        "procedural block");
    return arena_.Create<Stmt>();
  }
  switch (CurrentToken().kind) {
    case TokenKind::kKwBegin:
      return ParseBlockStmt(prefix_label);
    case TokenKind::kKwIf:
      return ParseIfStmt();
    case TokenKind::kKwCase:
    case TokenKind::kKwCasex:
    case TokenKind::kKwCasez:
      return ParseCaseStmt(CurrentToken().kind);
    case TokenKind::kKwFor:
      return ParseForStmt();
    case TokenKind::kKwForeach:
      return ParseForeachStmt();
    case TokenKind::kKwWhile:
      return ParseWhileStmt();
    case TokenKind::kKwForever:
      return ParseForeverStmt();
    case TokenKind::kKwRepeat:
      return ParseRepeatStmt();
    case TokenKind::kKwFork:
      return ParseForkStmt(prefix_label);
    case TokenKind::kKwDo:
      return ParseDoWhileStmt();
    case TokenKind::kKwBreak:
      return ParseSimpleKeywordStmt(StmtKind::kBreak);
    case TokenKind::kKwContinue:
      return ParseSimpleKeywordStmt(StmtKind::kContinue);
    case TokenKind::kKwReturn:
      return ParseReturnStmt();
    case TokenKind::kKwWait:
      return ParseWaitStmt();
    case TokenKind::kKwDisable:
      return ParseDisableStmt();
    case TokenKind::kHash:
      return ParseDelayStmt();
    case TokenKind::kHashHash:
      return ParseCycleDelayStmt();
    case TokenKind::kAt:
      return ParseEventControlStmt();
    case TokenKind::kArrow:
      return ParseEventTriggerStmt();
    case TokenKind::kDashGtGt:
      return ParseNbEventTriggerStmt();
    case TokenKind::kKwAssign:
      return ParseProceduralAssignStmt();
    case TokenKind::kKwDeassign:
      return ParseProceduralDeassignStmt();
    case TokenKind::kKwForce:
      return ParseForceStmt();
    case TokenKind::kKwRelease:
      return ParseReleaseStmt();
    case TokenKind::kKwAssert:
      return ParseImmediateAssert();
    case TokenKind::kKwAssume:
      return ParseImmediateAssume();
    case TokenKind::kKwCover:
      return ParseImmediateCover();
    case TokenKind::kKwRestrict:

      diag_.Error(CurrentLoc(),
                  "restrict has no immediate (procedural) form; "
                  "use `restrict property (...)` at module-item level",
                  Subclause("16.2"));
      Consume();
      return arena_.Create<Stmt>();
    case TokenKind::kKwWaitOrder:
      return ParseWaitOrderStmt();
    case TokenKind::kKwRandcase:
      return ParseRandcaseStmt();
    case TokenKind::kKwRandsequence:
      return ParseRandsequenceStmt();
    case TokenKind::kKwExpect:
      return ParseExpectStmt();
    default:
      return ParseAssignmentOrExprStmt();
  }
}

Stmt* Parser::ParseEventTriggerStmt() {
  auto* s = arena_.Create<Stmt>();
  s->kind = StmtKind::kEventTrigger;
  s->range.start = CurrentLoc();
  Consume();
  s->expr = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("15.5.1"));
  return s;
}

Stmt* Parser::ParseNbEventTriggerStmt() {
  auto* s = arena_.Create<Stmt>();
  s->kind = StmtKind::kNbEventTrigger;
  s->range.start = CurrentLoc();
  Consume();

  // delay_or_event_control = delay_control | event_control
  //                       | repeat ( expression ) event_control
  if (Check(TokenKind::kHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      s->delay = ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen, Subclause("15.5.1"));
    } else {
      s->delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kKwRepeat)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("15.5.1"));
    s->repeat_event_count = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("15.5.1"));
    Expect(TokenKind::kAt, Subclause("15.5.1"));
    Expect(TokenKind::kLParen, Subclause("15.5.1"));
    s->events = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("15.5.1"));
  } else if (Check(TokenKind::kAt)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      s->is_star_event = true;
    } else if (Check(TokenKind::kLParen)) {
      Consume();
      if (Match(TokenKind::kStar)) {
        s->is_star_event = true;
      } else {
        s->events = ParseEventList();
      }
      Expect(TokenKind::kRParen, Subclause("15.5.1"));
    } else {
      EventExpr ev;
      ev.signal = ParseExpr();
      s->events.push_back(ev);
    }
  }
  s->expr = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("15.5.1"));
  return s;
}

Stmt* Parser::ParseIfStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwIf, Subclause("12.4"));
  Expect(TokenKind::kLParen, Subclause("12.4"));
  stmt->condition = ParseExpr();
  SkipUnparenthesizedAssignInExpr();
  Expect(TokenKind::kRParen, Subclause("12.4"));
  stmt->then_branch = ParseStmt();
  if (Match(TokenKind::kKwElse)) {
    stmt->else_branch = ParseStmt();
  }
  return stmt;
}

Stmt* Parser::ParseCaseStmt(TokenKind case_kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = case_kind;
  stmt->range.start = CurrentLoc();
  Consume();
  Expect(TokenKind::kLParen, Subclause("12.5"));
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("12.5"));

  if (Check(TokenKind::kKwInside)) {
    auto inside_loc = CurrentLoc();
    Consume();
    if (case_kind != TokenKind::kKwCase) {
      diag_.Error(inside_loc, "'inside' is only valid with 'case'",
                  Subclause("12.5"));
    }
    stmt->case_inside = true;
  }

  if (Check(TokenKind::kKwMatches)) {
    auto matches_loc = CurrentLoc();
    Consume();
    if (stmt->case_inside) {
      diag_.Error(matches_loc, "'matches' and 'inside' cannot be used together",
                  Subclause("12.5"));
    }
    stmt->case_matches = true;
  }
  bool seen_default = false;
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    auto item_loc = CurrentLoc();
    bool is_default_here = Check(TokenKind::kKwDefault);
    stmt->case_items.push_back(ParseCaseItem(stmt->case_inside));
    if (is_default_here) {
      if (seen_default) {
        diag_.Error(item_loc,
                    "case statement shall have at most one 'default' item",
                    Subclause("12.5"));
      }
      seen_default = true;
    }
  }
  Expect(TokenKind::kKwEndcase, Subclause("12.5"));
  return stmt;
}

CaseItem Parser::ParseCaseItem(bool inside) {
  CaseItem item;
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
    Match(TokenKind::kColon);
  } else {
    item.patterns.push_back(inside ? ParseInsideValueRange() : ParseExpr());
    while (Match(TokenKind::kComma)) {
      item.patterns.push_back(inside ? ParseInsideValueRange() : ParseExpr());
    }
    Expect(TokenKind::kColon, Subclause("12.5"));
  }
  item.body = ParseStmt();
  return item;
}

Stmt* Parser::ParseForStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kFor;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwFor, Subclause("12.7.1"));
  Expect(TokenKind::kLParen, Subclause("12.7.1"));

  if (Check(TokenKind::kSemicolon)) {
    Consume();
  } else if (Check(TokenKind::kKwVar) ||
             IsDataTypeKeyword(CurrentToken().kind) ||
             (Check(TokenKind::kIdentifier) &&
              known_types_.count(CurrentToken().text) != 0)) {
    // for_variable_declaration ::= [ var ] data_type variable_identifier = ...
    // (Syntax 12-5). data_type may be a user-defined (named) type, so a leading
    // identifier that names a known type begins a local declaration rather than
    // a plain assignment.
    ParserStmtHelpers::ParseForLocalDeclInits(*this, stmt);
  } else {
    ParserStmtHelpers::ParseForPlainInits(*this, stmt);
  }

  if (!Check(TokenKind::kSemicolon)) {
    stmt->for_cond = ParseExpr();
  }
  Expect(TokenKind::kSemicolon, Subclause("12.7.1"));

  if (!Check(TokenKind::kRParen)) {
    do {
      stmt->for_steps.push_back(ParserStmtHelpers::ParseForStep(*this));
    } while (Match(TokenKind::kComma));
  }
  Expect(TokenKind::kRParen, Subclause("12.7.1"));
  stmt->for_body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseSimpleKeywordStmt(StmtKind kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Consume();
  Expect(TokenKind::kSemicolon, Subclause("12.8"));
  return stmt;
}

Stmt* Parser::ParseReturnStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kReturn;
  stmt->range.start = CurrentLoc();
  Consume();
  if (!Check(TokenKind::kSemicolon)) {
    stmt->expr = ParseExpr();
  }
  Expect(TokenKind::kSemicolon, Subclause("12.8"));
  return stmt;
}

Stmt* Parser::ParseWaitStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWait, Subclause("9.4.3"));

  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kWaitFork;
    Expect(TokenKind::kSemicolon, Subclause("9.6.1"));
    return stmt;
  }

  stmt->kind = StmtKind::kWait;
  Expect(TokenKind::kLParen, Subclause("9.4.3"));
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("9.4.3"));
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseDisableStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDisable, Subclause("9.6.2"));

  if (Match(TokenKind::kKwFork)) {
    stmt->kind = StmtKind::kDisableFork;
    Expect(TokenKind::kSemicolon, Subclause("9.6.3"));
    return stmt;
  }

  stmt->kind = StmtKind::kDisable;
  stmt->expr = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("9.6.2"));
  return stmt;
}

void Parser::ParseIntraAssignTiming(Stmt* stmt) {
  if (Check(TokenKind::kHashHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      stmt->cycle_delay = ParseExpr();
      Expect(TokenKind::kRParen, Subclause("14.16"));
    } else {
      stmt->cycle_delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kHash)) {
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      stmt->delay = ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen, Subclause("9.4.5"));
    } else {
      stmt->delay = ParsePrimaryExpr();
    }
  } else if (Check(TokenKind::kAt)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("9.4.5"));
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("9.4.5"));
  } else if (Check(TokenKind::kKwRepeat)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("9.4.5"));
    stmt->repeat_event_count = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("9.4.5"));
    Expect(TokenKind::kAt, Subclause("9.4.5"));
    Expect(TokenKind::kLParen, Subclause("9.4.5"));
    stmt->events = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("9.4.5"));
  }
  stmt->rhs = ParseMinTypMaxExpr();
}

Stmt* Parser::ParseAssignmentOrExprNoSemi() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();

  auto* lhs_expr = ParsePrefixExpr();

  if (Match(TokenKind::kEq)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    ParseIntraAssignTiming(stmt);
  } else if (Match(TokenKind::kLtEq)) {
    stmt->kind = StmtKind::kNonblockingAssign;
    stmt->lhs = lhs_expr;
    ParseIntraAssignTiming(stmt);
  } else if (IsCompoundAssignOp(CurrentToken().kind)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    auto op_tok = Consume();
    stmt->rhs = ParseExpr();
    stmt->delay = nullptr;

    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op_tok.kind;
    bin->lhs = lhs_expr;
    bin->rhs = stmt->rhs;
    bin->range.start = lhs_expr->range.start;
    stmt->rhs = bin;
  } else {
    stmt->kind = StmtKind::kExprStmt;
    stmt->expr = ParseInfixBp(lhs_expr, 0);
  }
  return stmt;
}

// A.6.9's second subroutine_call_statement, `void ' ( function_subroutine_call
// ) ;`, which §13.4.1 has discard a nonvoid function's return value without
// the warning a bare call draws. The cast wraps a function_subroutine_call
// and nothing else, so what stands inside the parentheses is read as an
// expression and reported under A.6.9 where it is no call; the statement is
// recorded as the expression statement over a `void` cast that the
// elaborator reads.
Stmt* Parser::ParseVoidCastCallStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kExprStmt;
  stmt->range.start = CurrentLoc();
  Token void_tok = Consume();
  Expect(TokenKind::kApostrophe, Subclause("A.6.9"));
  Expect(TokenKind::kLParen, Subclause("A.6.9"));
  Expr* call = ParseExpr();
  if (call->kind != ExprKind::kCall && call->kind != ExprKind::kSystemCall) {
    diag_.Error(call->range.start,
                "a void cast discards a function call's return value; "
                "void'(...) wraps a function_subroutine_call and no other "
                "expression",
                Subclause("A.6.9"));
  }
  Expect(TokenKind::kRParen, Subclause("A.6.9"));
  stmt->expr = MakeTextCast(arena_, void_tok.text, void_tok.loc, call);
  return stmt;
}

void Parser::SkipUnparenthesizedAssignInExpr() {
  if (!Check(TokenKind::kEq)) return;
  diag_.Error(
      CurrentLoc(),
      "an assignment within an expression must be enclosed in parentheses",
      Subclause("11.3.6"));
  while (Match(TokenKind::kEq)) ParseExpr();
}

Stmt* Parser::ParseAssignmentOrExprStmt() {
  auto* stmt = Check(TokenKind::kKwVoid) ? ParseVoidCastCallStmt()
                                         : ParseAssignmentOrExprNoSemi();
  SkipUnparenthesizedAssignInExpr();
  Expect(TokenKind::kSemicolon, Subclause("12.3"));
  return stmt;
}

Stmt* Parser::ParseCycleDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCycleDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHashHash, Subclause("14.11"));
  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->cycle_delay = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("14.11"));
  } else {
    stmt->cycle_delay = ParsePrimaryExpr();
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHash, Subclause("9.4.1"));

  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->delay = ParseMinTypMaxExpr();
    Expect(TokenKind::kRParen, Subclause("9.4.1"));
  } else {
    stmt->delay = ParsePrimaryExpr();
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseEventControlStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kEventControl;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kAt, Subclause("9.4.2"));
  if (Match(TokenKind::kStar)) {
    stmt->is_star_event = true;
  } else if (Check(TokenKind::kLParen)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      stmt->is_star_event = true;
    } else {
      stmt->events = ParseEventList();
    }
    Expect(TokenKind::kRParen, Subclause("9.4.2"));
  } else {
    EventExpr ev;
    ev.signal = ParseExpr();
    stmt->events.push_back(ev);
  }
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseProceduralAssignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwAssign, Subclause("10.6.1"));
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kEq, Subclause("10.6.1"));
  stmt->rhs = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("10.6.1"));
  return stmt;
}

Stmt* Parser::ParseProceduralDeassignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDeassign, Subclause("10.6.1"));
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("10.6.1"));
  return stmt;
}

Stmt* Parser::ParseForceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForce, Subclause("10.6.2"));
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kEq, Subclause("10.6.2"));
  stmt->rhs = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("10.6.2"));
  return stmt;
}

Stmt* Parser::ParseReleaseStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRelease, Subclause("10.6.2"));
  stmt->lhs = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("10.6.2"));
  return stmt;
}

}  // namespace delta
