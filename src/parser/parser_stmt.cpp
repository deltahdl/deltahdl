#include <algorithm>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"
#include "parser/parser_property_spec_internal.h"
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

  // Syntax 12-2 and Syntax 12-3 give `unique_priority` a place in front of
  // `if` and a case keyword and nowhere else, so a qualifier `qual_loc` holds
  // before any other statement is reported there.
  static void ApplyStmtQualifierAndAttrs(Parser& p, Stmt* stmt,
                                         CaseQualifier qual, SourceLoc qual_loc,
                                         std::vector<Attribute>& attrs) {
    if (!attrs.empty()) stmt->attrs = std::move(attrs);
    if (qual == CaseQualifier::kNone) return;
    stmt->qualifier = qual;
    if (stmt->kind == StmtKind::kIf) {
      CheckQualifiedElseIfBranches(p, stmt);
    } else if (stmt->kind != StmtKind::kCase) {
      p.diag_.Error(qual_loc,
                    "unique, unique0 and priority may qualify only an if or "
                    "a case statement",
                    Subclause("12.4"));
    }
  }

  // A.8.3: whether `e` is an inc_or_dec_expression, `x++` or `--x`.
  static bool IsIncOrDec(const Expr* e) {
    return (e->kind == ExprKind::kUnary ||
            e->kind == ExprKind::kPostfixUnary) &&
           (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
  }

  // A.6.4 with A.6.9: whether `e`, the expression of an expression statement,
  // is a form a statement_item takes: a subroutine call, written with its
  // argument list or as a task or method enable by a name, a scoped or
  // hierarchical name or a member select, any of them with the `with` clause
  // or inline constraint it carries; or an inc_or_dec_expression.
  static bool IsStatementExpr(const Expr* e) {
    return e->kind == ExprKind::kCall || e->kind == ExprKind::kSystemCall ||
           e->kind == ExprKind::kIdentifier ||
           e->kind == ExprKind::kMemberAccess || IsIncOrDec(e);
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

  // Syntax 12-5's for_variable_declaration opens with `var` or a data_type: a
  // type keyword, a type reference, a name this scope knows as a type, or a
  // type name behind a package scope (A.2.2.1), which a package name never is
  // a known type for.
  // The last is told from an assignment to a package's variable, `pkg::v = 0`,
  // by what follows the scoped name, as a block item is.
  static bool AtForLocalDecl(Parser& p) {
    if (p.Check(TokenKind::kKwVar) || p.Check(TokenKind::kKwType) ||
        IsDataTypeKeyword(p.CurrentToken().kind))
      return true;
    if (!p.Check(TokenKind::kIdentifier)) return false;
    if (p.known_types_.count(p.CurrentToken().text) != 0) return true;
    return p.AtScopedTypeName() && !p.IsScopedCallOrAssignStmt();
  }

  // A.6.8's for_variable_declaration names its data type once, before a
  // comma-separated list of `variable_identifier = expression`, and a later
  // for_variable_declaration of the same initialization names its own. An item
  // after the first that brings neither `var` nor a data type is therefore a
  // further variable of the declaration before it, and takes that data type:
  // Parser::ParseDeclaredDataType consumes nothing at such an item's identifier
  // and answers DataTypeKind::kImplicit, which every reader of
  // Stmt::for_init_types takes for an assignment rather than a declaration.
  static void ParseForLocalDeclInits(Parser& p, Stmt* stmt) {
    do {
      bool has_var = p.Match(TokenKind::kKwVar);
      // A.2.2.1 counts a type_reference among the data types, which the loop
      // variable, a variable, writes after `var` (§6.23).
      DataType type;
      if (!ParserDataDeclHelpers::ReadKeyedTypeReference(p, type, has_var,
                                                         false)) {
        type = p.ParseDeclaredDataType();
      }
      if (!has_var && type.kind == DataTypeKind::kImplicit &&
          type.type_ref_expr == nullptr && !stmt->for_init_types.empty()) {
        type = stmt->for_init_types.back();
      }
      stmt->for_init_types.push_back(type);
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
            "this for-loop initialization mixes a locally declared control "
            "variable with one declared outside the loop",
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
    return IsIncOrDec(e);
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

  // A.6.2 (printed page 1198) writes an assignment's right-hand side as an
  // expression, and A.8.3 (printed page 1210) gives the min:typ:max triple to
  // mintypmax_expression alone, which an expression reaches only as A.8.4's
  // parenthesized primary. The triple is read whole, so the statement's `;` is
  // where the parse goes on.
  static Expr* ParseAssignedExpr(Parser& p) {
    Expr* rhs = p.ParseMinTypMaxExpr();
    if (rhs->kind == ExprKind::kMinTypMax && !rhs->is_parenthesized) {
      p.diag_.Error(rhs->range.start,
                    "an assignment's right-hand side is an expression, which "
                    "holds a min:typ:max triple only within parentheses",
                    Subclause("A.6.2"));
    }
    return rhs;
  }

  // A.8.5's (printed page 1212) name form of an lvalue: a name, scoped or
  // reached through member selects, under any selects.
  static bool IsNamedLvalue(const Expr* e) {
    static constexpr ExprKind kNamed[] = {
        ExprKind::kIdentifier, ExprKind::kSelect, ExprKind::kMemberAccess};
    return std::ranges::any_of(kNamed,
                               [e](ExprKind kind) { return kind == e->kind; });
  }

  // Whether `e` has a form A.8.5 (printed page 1212) gives variable_lvalue,
  // which covers every form it gives net_lvalue: a name under selects, a
  // concatenation of such targets, an assignment pattern of them, typed or not,
  // or a streaming concatenation. None is written in parentheses. A
  // replication is left to §11.4.12.1's report on a target holding one.
  static bool HasLvalueForm(const Expr* e) {
    if (e->is_parenthesized) return false;
    if (e->kind == ExprKind::kCast) {
      return e->lhs->kind == ExprKind::kAssignmentPattern &&
             HasLvalueForm(e->lhs);
    }
    if (e->kind == ExprKind::kConcatenation ||
        e->kind == ExprKind::kAssignmentPattern) {
      return std::ranges::all_of(e->elements, HasLvalueForm);
    }
    return IsNamedLvalue(e) || e->kind == ExprKind::kStreamingConcat ||
           e->kind == ExprKind::kReplicate;
  }

  // A.6.2 (printed page 1198) writes the target of every procedural
  // assignment as a variable_lvalue, and a force's or a release's as that or a
  // net_lvalue.
  static void CheckLvalueForm(Parser& p, const Expr* target) {
    if (HasLvalueForm(target)) return;
    p.diag_.Error(target->range.start,
                  "this target is neither a variable_lvalue nor a net_lvalue",
                  Subclause("A.8.5"));
  }

  // Whether the parse stands at `new [`, the dynamic_array_new of A.2.4.
  static bool AtDynamicArrayNew(Parser& p) {
    if (!p.Check(TokenKind::kKwNew)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool sized = p.Check(TokenKind::kLBracket);
    p.lexer_.RestorePos(saved);
    return sized;
  }

  // A.6.2 (printed page 1198) admits a `new` as the whole right-hand side of a
  // blocking assignment in two forms: a dynamic_array_new assigned to a
  // nonrange_variable_lvalue, a name whose selects hold no part-select, and a
  // class_new assigned to a name under any select. Neither is a concatenation,
  // a streaming concatenation or an assignment pattern.
  static void CheckNewTarget(Parser& p, const Stmt* stmt, bool dynamic_new) {
    if (!IsNewExpr(stmt->rhs)) return;
    if (!IsNamedLvalue(stmt->lhs)) {
      p.diag_.Error(stmt->lhs->range.start,
                    "a 'new' is assigned to a variable, never to a "
                    "concatenation, a streaming concatenation or an "
                    "assignment pattern",
                    Subclause("A.6.2"));
      return;
    }
    if (!dynamic_new) return;
    for (const Expr* e = stmt->lhs; e->kind == ExprKind::kSelect; e = e->base) {
      if (e->index_end == nullptr) continue;
      p.diag_.Error(stmt->lhs->range.start,
                    "a dynamic array's 'new' is assigned to a target with no "
                    "part-select",
                    Subclause("A.6.2"));
      return;
    }
  }

  // A.6.5's event_control after its `@`: `*`, `( * )`, a parenthesized
  // event_expression, or the name Parser::ParseNamedClockingEvent reads, kept
  // on `stmt` as an event control statement keeps it. A delay_or_event_control
  // holds one after an assignment operator and after `->>`, directly or after
  // a repeat count, and every form is read in each place. `subclause` is the
  // rule the closing parenthesis is expected under.
  static void ParseEventControlAfterAt(Parser& p, Stmt* stmt,
                                       Subclause subclause) {
    if (p.Match(TokenKind::kStar)) {
      stmt->is_star_event = true;
    } else if (p.Match(TokenKind::kLParen)) {
      if (p.Match(TokenKind::kStar)) {
        stmt->is_star_event = true;
      } else {
        stmt->events = p.ParseEventList();
      }
      p.Expect(TokenKind::kRParen, subclause);
    } else {
      stmt->events.push_back(p.ParseNamedClockingEvent());
    }
  }

  // A.6.5 writes an event trigger's operand, after `->` or `->>`, as a
  // hierarchical_event_identifier and a nonrange_select, the bit-selects and
  // member selects A.8.4 writes after it. Reads the operand into `s`.
  static void ParseEventTriggerOperand(Parser& p, Stmt* s) {
    s->expr = p.ParseExpr();
    if (IsHierarchicalName(s->expr, true)) return;
    p.diag_.Error(s->expr->range.start,
                  "an event trigger names an event: a hierarchical identifier "
                  "and its bit-selects",
                  Subclause("A.6.5"));
  }

  // The first of a case item's expressions: under `inside` a range_list's
  // value_range, and under `matches` a case_pattern_item's pattern with its
  // optional `&&&` filter (A.6.7). Those two are read through ParseExprBp,
  // which leaves the `&&&` unreported where Parser::ParseExpr would report
  // it, with a pattern open around the pattern.
  static Expr* ParseCaseItemHead(Parser& p, bool inside, bool matches) {
    if (inside) return p.ParseInsideValueRange();
    if (!matches) return p.ParseExpr();
    ++p.pattern_depth_;
    Expr* head = p.ParseExprBp(0);
    --p.pattern_depth_;
    CheckCasePatternHead(p, head);
    return head;
  }

  // Whether `e` is the operator `op` written bare. One in parentheses was
  // reported where it stands, by Parser::ParseExpr.
  static bool IsBarePredicate(const Expr* e, TokenKind op) {
    return e->kind == ExprKind::kBinary && e->op == op && !e->is_parenthesized;
  }

  // A.6.7 writes a case_pattern_item as a pattern and at most one `&&&`
  // filter, which is an expression, and neither `&&&` nor `matches` is a
  // binary operator (A.8.6). So no `matches` follows the pattern, and the
  // filter holds neither a second `&&&` nor a `matches`.
  static void CheckCasePatternHead(Parser& p, const Expr* head) {
    const Expr* pattern = head;
    while (IsBarePredicate(pattern, TokenKind::kAmpAmpAmp))
      pattern = pattern->lhs;
    if (IsBarePredicate(pattern, TokenKind::kKwMatches)) {
      p.diag_.Error(head->range.start,
                    "a pattern-matching case item's pattern takes a '&&&' "
                    "filter, not 'matches'",
                    Subclause("A.6.7"));
    }
    if (IsBarePredicate(head, TokenKind::kAmpAmpAmp) &&
        (IsBarePredicate(head->lhs, TokenKind::kAmpAmpAmp) ||
         IsBarePredicate(head->rhs, TokenKind::kKwMatches))) {
      p.diag_.Error(head->range.start,
                    "a pattern-matching case item takes one '&&&' filter, "
                    "which is an expression",
                    Subclause("A.6.7"));
    }
  }

  // A.6.5's `repeat ( expression ) event_control`, its `repeat` already read.
  static void ParseRepeatEventControl(Parser& p, Stmt* stmt,
                                      Subclause subclause) {
    p.Expect(TokenKind::kLParen, subclause);
    stmt->repeat_event_count = p.ParseExpr();
    p.Expect(TokenKind::kRParen, subclause);
    p.Expect(TokenKind::kAt, subclause);
    ParseEventControlAfterAt(p, stmt, subclause);
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
  SourceLoc label_loc = CurrentLoc();
  auto prefix_label = TryParseStmtLabel();
  auto attrs = ParseAttributes();

  if (Match(TokenKind::kSemicolon)) {
    // A.6.4 writes statement_or_null's null form as attribute instances and
    // a semicolon, and the label belongs to a statement, whose statement_item
    // is never a bare semicolon.
    if (!prefix_label.empty()) {
      diag_.Error(label_loc,
                  "a null statement takes attribute instances and no label",
                  Subclause("A.6.4"));
    }
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kNull;
    stmt->label = prefix_label;
    stmt->attrs = std::move(attrs);
    return stmt;
  }

  auto qual = TokenToCaseQualifier(CurrentToken().kind);
  SourceLoc qual_loc = CurrentLoc();
  if (qual != CaseQualifier::kNone) {
    Consume();
  }

  Stmt* stmt = ParseStmtBody(prefix_label);
  if (stmt != nullptr) {
    ParserStmtHelpers::ApplyStmtLabel(*this, stmt, prefix_label);
    ParserStmtHelpers::ApplyStmtQualifierAndAttrs(*this, stmt, qual, qual_loc,
                                                  attrs);
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
        "a clocking block cannot stand as a statement of a function, a task or "
        "a procedural block");
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
      return ParserPropertySpecHelpers::ParseProceduralRestrict(*this);
    case TokenKind::kKwWaitOrder:
      return ParseWaitOrderStmt();
    case TokenKind::kKwRandcase:
      return ParseRandcaseStmt();
    case TokenKind::kKwRandsequence:
      return ParseRandsequenceStmt();
    case TokenKind::kKwExpect:
      return ParseExpectStmt();
    default:
      if (AtCheckerInstantiationStmt()) return ParseCheckerInstantiationStmt();
      return ParseAssignmentOrExprStmt();
  }
}

Stmt* Parser::ParseEventTriggerStmt() {
  auto* s = arena_.Create<Stmt>();
  s->kind = StmtKind::kEventTrigger;
  s->range.start = CurrentLoc();
  Consume();
  ParserStmtHelpers::ParseEventTriggerOperand(*this, s);
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
      s->delay = ParseDelayValue();
    }
  } else if (Match(TokenKind::kKwRepeat)) {
    ParserStmtHelpers::ParseRepeatEventControl(*this, s, Subclause("15.5.1"));
  } else if (Match(TokenKind::kAt)) {
    ParserStmtHelpers::ParseEventControlAfterAt(*this, s, Subclause("15.5.1"));
  }
  ParserStmtHelpers::ParseEventTriggerOperand(*this, s);
  Expect(TokenKind::kSemicolon, Subclause("15.5.1"));
  return s;
}

Stmt* Parser::ParseIfStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwIf, Subclause("12.4"));
  Expect(TokenKind::kLParen, Subclause("12.4"));
  // A.6.6: the condition is a cond_predicate, which Parser::ParseExpr reports
  // wherever else its `matches` or `&&&` stands.
  stmt->condition = ParseExprBp(0);
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
    stmt->case_items.push_back(
        ParseCaseItem(stmt->case_inside, stmt->case_matches));
    if (is_default_here) {
      if (seen_default) {
        diag_.Error(item_loc,
                    "case statement shall have at most one 'default' item",
                    Subclause("12.5"));
      }
      seen_default = true;
    }
  }
  // Syntax 12-3 writes each case form with `case_item { case_item }`, the
  // pattern and inside items alike, so at least one item, default among them,
  // stands before endcase.
  if (stmt->case_items.empty()) {
    diag_.Error(CurrentLoc(),
                "case statement shall have at least one case item",
                Subclause("12.5"));
  }
  Expect(TokenKind::kKwEndcase, Subclause("12.5"));
  return stmt;
}

// Syntax 12-3: a case_item lists case_item_expressions, a case_inside_item a
// range_list, and a case_pattern_item (`matches`) one pattern, so a comma after
// that pattern is reported; the list is still read so the item's colon is
// found.
CaseItem Parser::ParseCaseItem(bool inside, bool matches) {
  CaseItem item;
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
    Match(TokenKind::kColon);
  } else {
    item.patterns.push_back(
        ParserStmtHelpers::ParseCaseItemHead(*this, inside, matches));
    if (matches && Check(TokenKind::kComma)) {
      diag_.Error(CurrentLoc(),
                  "a pattern-matching case item holds one pattern, not a list",
                  Subclause("12.6.1"));
    }
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
  } else if (ParserStmtHelpers::AtForLocalDecl(*this)) {
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
  // A.6.5: the target is a hierarchical_task_identifier or a
  // hierarchical_block_identifier, each an A.9.3 hierarchical_identifier.
  if (!IsHierarchicalName(stmt->expr, false)) {
    diag_.Error(stmt->expr->range.start,
                "a disable statement names a task or a block, which is a "
                "hierarchical identifier",
                Subclause("A.6.5"));
  }
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
      stmt->delay = ParseDelayValue();
    }
  } else if (Match(TokenKind::kAt)) {
    ParserStmtHelpers::ParseEventControlAfterAt(*this, stmt,
                                                Subclause("9.4.5"));
  } else if (Match(TokenKind::kKwRepeat)) {
    ParserStmtHelpers::ParseRepeatEventControl(*this, stmt, Subclause("9.4.5"));
  }
  stmt->rhs = ParserStmtHelpers::ParseAssignedExpr(*this);
}

Stmt* Parser::ParseAssignmentOrExprNoSemi() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->range.start = CurrentLoc();

  auto* lhs_expr = ParsePrefixExpr();

  if (Match(TokenKind::kEq)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    bool dynamic_new = ParserStmtHelpers::AtDynamicArrayNew(*this);
    ParseIntraAssignTiming(stmt);
    ParserStmtHelpers::CheckNewTarget(*this, stmt, dynamic_new);
  } else if (Match(TokenKind::kLtEq)) {
    stmt->kind = StmtKind::kNonblockingAssign;
    stmt->lhs = lhs_expr;
    ParseIntraAssignTiming(stmt);
  } else if (IsCompoundAssignOp(CurrentToken().kind)) {
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = lhs_expr;
    auto op_tok = Consume();
    stmt->rhs = ParserStmtHelpers::ParseAssignedExpr(*this);
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
    // A.6.9: a subroutine call statement is a call, and a `new` is no call:
    // §8.7 calls a constructor from the right-hand side of an assignment or
    // as `super.new`.
    if (IsNewExpr(stmt->expr)) {
      diag_.Error(stmt->expr->range.start,
                  "'new' is no subroutine call; a constructor is called from "
                  "the right-hand side of an assignment",
                  Subclause("A.6.9"));
    }
  }
  if (stmt->kind != StmtKind::kExprStmt) {
    ParserStmtHelpers::CheckLvalueForm(*this, lhs_expr);
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
  // A.8.2: an array manipulation call or a randomize call may be written with
  // its `with` clause and no argument list, which the expression keeps on the
  // name it is written on rather than as a call.
  if (call->kind != ExprKind::kCall && call->kind != ExprKind::kSystemCall &&
      call->with_expr == nullptr && call->inline_constraint == nullptr) {
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
  Stmt* stmt = nullptr;
  if (Check(TokenKind::kKwVoid)) {
    stmt = ParseVoidCastCallStmt();
  } else {
    stmt = ParseAssignmentOrExprNoSemi();
    // A.6.4: no statement_item is an expression followed by `;` but a call
    // or an increment or decrement, so `x + 1;` and `a == b;` are none.
    if (stmt->kind == StmtKind::kExprStmt &&
        !ParserStmtHelpers::IsStatementExpr(stmt->expr)) {
      diag_.Error(stmt->expr->range.start,
                  "an expression statement is a subroutine call or an "
                  "increment or decrement; this expression is neither",
                  Subclause("A.6.4"));
    }
  }
  SkipUnparenthesizedAssignInExpr();
  Expect(TokenKind::kSemicolon, Subclause("12.3"));
  return stmt;
}

Stmt* Parser::ParseProceduralAssignStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwAssign, Subclause("10.6.1"));
  stmt->lhs = ParseExpr();
  ParserStmtHelpers::CheckLvalueForm(*this, stmt->lhs);
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
  ParserStmtHelpers::CheckLvalueForm(*this, stmt->lhs);
  Expect(TokenKind::kSemicolon, Subclause("10.6.1"));
  return stmt;
}

Stmt* Parser::ParseForceStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForce, Subclause("10.6.2"));
  stmt->lhs = ParseExpr();
  ParserStmtHelpers::CheckLvalueForm(*this, stmt->lhs);
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
  ParserStmtHelpers::CheckLvalueForm(*this, stmt->lhs);
  Expect(TokenKind::kSemicolon, Subclause("10.6.2"));
  return stmt;
}

}  // namespace delta
