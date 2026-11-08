#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "parser/parser.h"
#include "parser/parser_property_grammar.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

static void ExpectDeferredHashZero(DiagEngine& diag, const Token& tok) {
  if (tok.text != "0") {
    diag.Error(tok.loc,
               "deferred immediate assertion requires #0, got #" +
                   std::string(tok.text),
               Subclause("16.4"));
  }
}

static ModuleItem* EndedAtLastToken(ModuleItem* item, const Lexer& lexer) {
  item->end = lexer.TakenEnd();
  if (item->body != nullptr && item->body->is_deferred) {
    item->body->range.end = item->end;
  }
  return item;
}

static Stmt* Spanning(Stmt* stmt, SourceLoc start, const Lexer& lexer) {
  stmt->range = {start, lexer.TakenEnd()};
  return stmt;
}

struct ParserAssertHelpers {
  static void RejectDeferredInProgram(Parser& p, SourceLoc loc) {
    p.RejectInProgramBody(loc,
                          "a deferred immediate assertion is not an item of a "
                          "program; outside procedural code it stands for an "
                          "always_comb procedure, which a program does not "
                          "contain");
  }

  static void ParseDeferral(Parser& p, Stmt* stmt) {
    if (p.Match(TokenKind::kHash)) {
      auto tok = p.Expect(TokenKind::kIntLiteral, Subclause("16.4"));
      ExpectDeferredHashZero(p.diag_, tok);
      stmt->is_deferred = true;
    } else if (p.Match(TokenKind::kKwFinal)) {
      stmt->is_deferred = true;
      stmt->is_final_deferred = true;
    }
  }

  static void ParseAssertedExpr(Parser& p, Stmt* stmt) {
    p.Expect(TokenKind::kLParen, Subclause("16.3"));
    stmt->assert_expr = p.ParseExpr();
    p.Expect(TokenKind::kRParen, Subclause("16.3"));
  }

  static void ParseActionBlock(Parser& p, Stmt*& pass_stmt, Stmt*& fail_stmt) {
    SourceLoc pass_loc = p.CurrentLoc();
    if (!p.Check(TokenKind::kSemicolon) && !p.Check(TokenKind::kKwElse)) {
      pass_stmt = p.ParseStmt();
    }
    if (p.Match(TokenKind::kKwElse)) {
      if (pass_stmt != nullptr && pass_stmt->kind == StmtKind::kNull) {
        p.diag_.Error(pass_loc,
                      "an action block's statement before 'else' is a "
                      "statement, which cannot be null",
                      Subclause("A.6.3"));
      }
      fail_stmt = p.ParseStmt();
    }
    if (!pass_stmt && !fail_stmt) {
      p.Expect(TokenKind::kSemicolon, Subclause("16.3"));
    }
  }

  static void ParseCoverTail(Parser& p, Stmt* stmt, Subclause semicolon,
                             Subclause no_fail) {
    if (p.Check(TokenKind::kSemicolon)) {
      p.Expect(TokenKind::kSemicolon, semicolon);
    } else if (!p.Check(TokenKind::kKwElse)) {
      stmt->assert_pass_stmt = p.ParseStmt();
    }
    if (!p.Check(TokenKind::kKwElse)) return;
    p.diag_.Error(p.CurrentLoc(),
                  "cover has no fail statement; the else arm belongs to assert "
                  "and assume",
                  no_fail);
    p.Expect(TokenKind::kKwElse, no_fail);
    p.ParseStmt();
  }

  static ModuleItem* ParseDeferredCoverItem(Parser& p, SourceLoc loc);

  static void RejectOutsideAlwaysOrInitial(Parser& p, SourceLoc loc) {
    if (p.always_or_initial_depth_ != 0 || p.cover_pass_statement_depth_ != 0) {
      return;
    }
    p.diag_.Error(loc,
                  "a concurrent assertion statement in procedural code shall "
                  "be in an always or an initial procedure",
                  Subclause("16.14"));
  }
};

static void SkipBalancedPropertySpec(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
}

Stmt* Parser::ParseProceduralConcurrentAssertLike(StmtKind kind) {
  SourceLoc loc = CurrentLoc();
  ParserAssertHelpers::RejectOutsideAlwaysOrInitial(*this, loc);
  bool sequence = Match(TokenKind::kKwSequence);
  if (!sequence) Expect(TokenKind::kKwProperty, Subclause("16.14.6"));
  Stmt* stmt =
      ParseProceduralPropertySpec(kind, loc, Subclause("16.14.6"), sequence);
  stmt->cover_sequence = sequence;
  if (kind == StmtKind::kCoverImmediate) {
    ParserAssertHelpers::ParseCoverTail(*this, stmt, Subclause("16.14.3"),
                                        Subclause("16.14.3"));
  } else {
    ParserAssertHelpers::ParseActionBlock(*this, stmt->assert_pass_stmt,
                                          stmt->assert_fail_stmt);
  }
  return stmt;
}

Stmt* Parser::ParseProceduralPropertySpec(StmtKind kind, SourceLoc loc,
                                          Subclause subclause, bool sequence) {
  auto* spec = arena_.Create<ModuleItem>();
  spec->loc = loc;
  Expect(TokenKind::kLParen, subclause);
  bool admitted =
      !sequence || ParserPropertyGrammar::CheckPropertySpec(*this, true);
  Stmt* stmt = nullptr;
  if (TryParseSimpleConcurrentProperty(spec, kind)) {
    stmt = spec->body;
    stmt->assert_clock = spec->sensitivity;
  } else {
    stmt = arena_.Create<Stmt>();
    stmt->kind = kind;
    stmt->range.start = spec->loc;
    if (!sequence) {
      admitted = ParserPropertyGrammar::CheckPropertySpec(*this, false);
    }
    if (admitted) {
      diag_.Warning(spec->loc,
                    "procedural concurrent assertion is not evaluated: its "
                    "property_spec holds more than the forms this tool "
                    "evaluates",
                    Subclause("16.14.6"));
    }
    SkipBalancedPropertySpec(lexer_);
  }
  stmt->is_procedural_concurrent = true;
  Expect(TokenKind::kRParen, subclause);
  return stmt;
}

Stmt* Parser::ParseImmediateAssertLike(StmtKind kind, TokenKind keyword) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Expect(keyword, Subclause("16.3"));

  if (Check(TokenKind::kKwProperty)) {
    return Spanning(ParseProceduralConcurrentAssertLike(kind),
                    stmt->range.start, lexer_);
  }

  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseActionBlock(*this, stmt->assert_pass_stmt,
                                        stmt->assert_fail_stmt);
  return Spanning(stmt, stmt->range.start, lexer_);
}

Stmt* Parser::ParseImmediateAssert() {
  return ParseImmediateAssertLike(StmtKind::kAssertImmediate,
                                  TokenKind::kKwAssert);
}

Stmt* Parser::ParseImmediateAssume() {
  return ParseImmediateAssertLike(StmtKind::kAssumeImmediate,
                                  TokenKind::kKwAssume);
}

Stmt* Parser::ParseImmediateCover() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCoverImmediate;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwCover, Subclause("16.3"));

  if (Check(TokenKind::kKwProperty) || Check(TokenKind::kKwSequence)) {
    return Spanning(
        ParseProceduralConcurrentAssertLike(StmtKind::kCoverImmediate),
        stmt->range.start, lexer_);
  }

  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseCoverTail(*this, stmt, Subclause("16.3"),
                                      Subclause("16.3"));
  return Spanning(stmt, stmt->range.start, lexer_);
}

static Expr* SkipPropertySpec(Arena& arena, Lexer& lexer, SourceLoc loc) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
  return ParserPropertySpecHelpers::PropertySpecPlaceholder(arena, loc);
}

static bool IsDeferredImmediate(Lexer& lexer) {
  if (lexer.Peek().Is(TokenKind::kHash)) return true;
  if (lexer.Peek().Is(TokenKind::kKwFinal)) return true;
  return false;
}

static ModuleItem* WrapStmtAsItem(Arena& arena, Stmt* stmt, SourceLoc loc,
                                  const Lexer& lexer) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAssertProperty;
  item->loc = loc;
  item->body = stmt;
  return EndedAtLastToken(item, lexer);
}

ModuleItem* ParserAssertHelpers::ParseDeferredCoverItem(Parser& p,
                                                        SourceLoc loc) {
  RejectDeferredInProgram(p, loc);
  auto* stmt = p.arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCoverImmediate;
  stmt->range.start = loc;
  stmt->is_deferred = true;
  if (p.Match(TokenKind::kHash)) {
    auto tok = p.Expect(TokenKind::kIntLiteral, Subclause("16.4"));
    ExpectDeferredHashZero(p.diag_, tok);
  } else if (p.Match(TokenKind::kKwFinal)) {
    stmt->is_final_deferred = true;
  }
  p.Expect(TokenKind::kLParen, Subclause("16.4"));
  stmt->assert_expr = p.ParseExpr();
  p.Expect(TokenKind::kRParen, Subclause("16.4"));
  ParseCoverTail(p, stmt, Subclause("16.4"), Subclause("16.3"));
  return WrapStmtAsItem(p.arena_, stmt, loc, p.lexer_);
}

ModuleItem* Parser::ParseDeferredImmediateItem(SourceLoc loc, StmtKind kind) {
  ParserAssertHelpers::RejectDeferredInProgram(*this, loc);
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = loc;
  stmt->is_deferred = true;
  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseActionBlock(*this, stmt->assert_pass_stmt,
                                        stmt->assert_fail_stmt);
  return WrapStmtAsItem(arena_, stmt, loc, lexer_);
}

bool Parser::BodyHasTemporalOperator() {
  auto scan = lexer_.SavePos();
  int depth = 0;
  bool found = false;
  while (!Check(TokenKind::kEof) && !Check(TokenKind::kKwEndproperty)) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kLParen) {
      ++depth;
    } else if (k == TokenKind::kRParen) {
      if (depth == 0) break;
      --depth;
    } else if (k == TokenKind::kSemicolon && depth == 0) {
      break;
    } else if (k == TokenKind::kPipeDashGt || k == TokenKind::kPipeEqGt ||
               k == TokenKind::kHashHash) {
      found = true;
      break;
    }
    Consume();
  }
  lexer_.RestorePos(scan);
  return found;
}

void Parser::WarnUnevaluatedConcurrentAssertion(SourceLoc loc) {
  diag_.Warning(loc,
                "concurrent assertion is not evaluated: its property_spec "
                "holds more than the @(event) boolean_expression this tool "
                "evaluates",
                Subclause("16.14"));
}

bool Parser::TryParseDisableIff(Expr*& disable_iff) {
  if (!Match(TokenKind::kKwDisable)) return true;
  if (!Match(TokenKind::kKwIff) || !Match(TokenKind::kLParen)) return false;
  disable_iff = ParserPropertySpecHelpers::ParseExpressionOrDist(*this);
  return disable_iff != nullptr && Match(TokenKind::kRParen);
}

bool Parser::TryParseSimpleConcurrentProperty(ModuleItem* item,
                                              StmtKind body_kind) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  std::vector<EventExpr> events;
  bool ok = true;
  while (ok && Match(TokenKind::kAt)) {
    events.clear();
    if (Match(TokenKind::kLParen)) {
      events = ParseEventList();
      if (!Match(TokenKind::kRParen)) ok = false;
    } else {
      events.push_back(ParseNamedClockingEvent());
    }
  }
  SimpleSpecBody body;
  if (ok) ok = TryParseDisableIff(body.disable_iff);
  if (ok) ok = ParserPropertySpecHelpers::ParseSimpleSpecBody(*this, body);
  if (!ok || !Check(TokenKind::kRParen)) {
    diag_.PopSuppress();
    lexer_.RestorePos(saved);
    return false;
  }
  diag_.PopSuppress();
  auto end = lexer_.SavePos();
  lexer_.RestorePos(saved);
  ParserPropertySpecHelpers::CheckSpecDistDefaults(*this);
  lexer_.RestorePos(end);
  item->sensitivity = std::move(events);
  item->body = ParserPropertySpecHelpers::MakeSimplePropertyStmt(
      *this, item, body_kind, body);
  return true;
}

static Expr* QualifiedInstanceName(Expr* instance, Arena& arena) {
  if (instance == nullptr || instance->kind != ExprKind::kMemberAccess ||
      instance->is_scope_resolution || instance->lhs == nullptr ||
      instance->rhs == nullptr ||
      instance->lhs->kind != ExprKind::kIdentifier ||
      instance->rhs->kind != ExprKind::kIdentifier) {
    return instance;
  }
  auto* qualified =
      arena.Create<std::string>(std::string(instance->lhs->text) + "." +
                                std::string(instance->rhs->text));
  instance->kind = ExprKind::kIdentifier;
  instance->text = *qualified;
  instance->lhs = nullptr;
  instance->rhs = nullptr;
  return instance;
}

bool Parser::TryParsePropertyInstanceSpec(ModuleItem* item) {
  if (!Check(TokenKind::kIdentifier)) return false;
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Expr* instance = ParserPropertySpecHelpers::TryParsePropertyInstance(*this);
  if (instance == nullptr) instance = ParseExpr();
  diag_.PopSuppress();
  instance = QualifiedInstanceName(instance, arena_);
  bool is_scoped =
      instance != nullptr &&
      (instance->kind == ExprKind::kMemberAccess ||
       (instance->kind == ExprKind::kCall && instance->callee.empty())) &&
      !InstanceDeclName(instance).empty();
  bool is_instance = instance != nullptr && Check(TokenKind::kRParen) &&
                     (instance->kind == ExprKind::kIdentifier ||
                      instance->kind == ExprKind::kCall || is_scoped);
  if (!is_instance) {
    lexer_.RestorePos(saved);
    return false;
  }
  if (is_scoped) {
    item->prop_instance_name =
        *arena_.Create<std::string>(InstanceDeclName(instance));
  } else {
    item->prop_instance_name =
        instance->kind == ExprKind::kCall ? instance->callee : instance->text;
  }
  item->assert_expr = instance;
  return true;
}

bool Parser::ReadStaticPropertySpec(ModuleItem* item, StmtKind body_kind) {
  if (Check(TokenKind::kAt)) {
    return TryParseSimpleConcurrentProperty(item, body_kind);
  }
  if (TryParsePropertyInstanceSpec(item)) return false;
  return TryParseSimpleConcurrentProperty(item, body_kind);
}

ModuleItem* Parser::ParsePropertyAssertLike(ModuleItemKind kind,
                                            TokenKind keyword) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = kind;
  item->loc = CurrentLoc();
  Expect(keyword, Subclause("16.14"));

  if (IsDeferredImmediate(lexer_)) {
    StmtKind sk = (kind == ModuleItemKind::kAssertProperty)
                      ? StmtKind::kAssertImmediate
                      : StmtKind::kAssumeImmediate;
    return ParseDeferredImmediateItem(item->loc, sk);
  }

  Expect(TokenKind::kKwProperty, Subclause("16.14"));
  Expect(TokenKind::kLParen, Subclause("16.14"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kRParen);
  StmtKind body_kind = kind == ModuleItemKind::kAssertProperty
                           ? StmtKind::kAssertImmediate
                           : StmtKind::kAssumeImmediate;
  bool simple_concurrent = ReadStaticPropertySpec(item, body_kind);
  if (!simple_concurrent && item->prop_instance_name.empty()) {
    if (ParserPropertyGrammar::CheckPropertySpec(*this, false)) {
      WarnUnevaluatedConcurrentAssertion(item->loc);
    }
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen, Subclause("16.14"));

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    item->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    item->assert_fail_stmt = ParseStmt();
  }
  if (!item->assert_pass_stmt && !item->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon, Subclause("16.14"));
  }
  if (simple_concurrent) {
    item->body->assert_pass_stmt = item->assert_pass_stmt;
    item->body->assert_fail_stmt = item->assert_fail_stmt;
  }
  return EndedAtLastToken(item, lexer_);
}

ModuleItem* Parser::ParseAssertProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssertProperty,
                                 TokenKind::kKwAssert);
}

ModuleItem* Parser::ParseAssumeProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssumeProperty,
                                 TokenKind::kKwAssume);
}

ModuleItem* Parser::ParseCoverProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCoverProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCover, Subclause("16.14.3"));

  if (IsDeferredImmediate(lexer_)) {
    return ParserAssertHelpers::ParseDeferredCoverItem(*this, item->loc);
  }

  if (Check(TokenKind::kKwSequence)) {
    item->kind = ModuleItemKind::kCoverSequence;
    Expect(TokenKind::kKwSequence, Subclause("16.14.3"));
  } else {
    Expect(TokenKind::kKwProperty, Subclause("16.14.3"));
  }

  Expect(TokenKind::kLParen, Subclause("16.14.3"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kRParen);
  const bool kSequence = item->kind == ModuleItemKind::kCoverSequence;
  bool admitted =
      !kSequence || ParserPropertyGrammar::CheckPropertySpec(*this, true);
  bool simple_concurrent =
      ReadStaticPropertySpec(item, StmtKind::kCoverImmediate);
  if (!simple_concurrent && item->prop_instance_name.empty()) {
    if (!kSequence) {
      admitted = ParserPropertyGrammar::CheckPropertySpec(*this, false);
    }
    if (admitted) WarnUnevaluatedConcurrentAssertion(item->loc);
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen, Subclause("16.14.3"));

  if (!Check(TokenKind::kSemicolon)) {
    ++cover_pass_statement_depth_;
    item->assert_pass_stmt = ParseStmt();
    --cover_pass_statement_depth_;
  } else {
    Expect(TokenKind::kSemicolon, Subclause("16.14.3"));
  }
  if (simple_concurrent) {
    item->body->assert_pass_stmt = item->assert_pass_stmt;
    item->body->cover_sequence = item->kind == ModuleItemKind::kCoverSequence;
  }
  return EndedAtLastToken(item, lexer_);
}

static bool IsConcurrentAssertionKeyword(TokenKind kind) {
  return kind == TokenKind::kKwAssert || kind == TokenKind::kKwAssume ||
         kind == TokenKind::kKwCover || kind == TokenKind::kKwRestrict;
}

ModuleItem* ParserPropertySpecHelpers::TryParseAlwaysConcurrentAssertion(
    Parser& p) {
  if (!IsConcurrentAssertionKeyword(p.CurrentToken().kind)) return nullptr;
  auto saved = p.lexer_.SavePos();
  TokenKind keyword = p.Consume().kind;
  bool is_concurrent =
      p.Check(TokenKind::kKwProperty) || p.Check(TokenKind::kKwSequence);
  p.lexer_.RestorePos(saved);
  if (!is_concurrent) return nullptr;
  switch (keyword) {
    case TokenKind::kKwAssert:
      return p.ParseAssertProperty();
    case TokenKind::kKwAssume:
      return p.ParseAssumeProperty();
    case TokenKind::kKwCover:
      return p.ParseCoverProperty();
    default:
      return p.ParseRestrictProperty();
  }
}

Stmt* ParserPropertySpecHelpers::ParseProceduralRestrict(Parser& p) {
  auto* stmt = p.arena_.Create<Stmt>();
  stmt->kind = StmtKind::kNull;
  stmt->range.start = p.CurrentLoc();
  p.Consume();
  if (!p.Match(TokenKind::kKwProperty)) {
    p.diag_.Error(stmt->range.start,
                  "restrict has no immediate form; a restrict assertion is "
                  "written `restrict property (...)`",
                  Subclause("16.2"));
    return stmt;
  }
  ParserAssertHelpers::RejectOutsideAlwaysOrInitial(p, stmt->range.start);
  p.Expect(TokenKind::kLParen, Subclause("16.14.4"));
  ParserPropertyGrammar::CheckPropertySpec(p, false);
  SkipBalancedPropertySpec(p.lexer_);
  p.Expect(TokenKind::kRParen, Subclause("16.14.4"));
  p.Expect(TokenKind::kSemicolon, Subclause("16.14.4"));
  return Spanning(stmt, stmt->range.start, p.lexer_);
}

ModuleItem* Parser::ParseRestrictProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kRestrictProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwRestrict, Subclause("16.14.4"));
  Expect(TokenKind::kKwProperty, Subclause("16.14.4"));
  Expect(TokenKind::kLParen, Subclause("16.14.4"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kRParen);
  if (!ReadStaticPropertySpec(item, StmtKind::kAssumeImmediate) &&
      item->prop_instance_name.empty()) {
    ParserPropertyGrammar::CheckPropertySpec(*this, false);
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen, Subclause("16.14.4"));
  Expect(TokenKind::kSemicolon, Subclause("16.14.4"));
  return EndedAtLastToken(item, lexer_);
}

Stmt* Parser::ParseExpectStmt() {
  SourceLoc loc = CurrentLoc();
  Expect(TokenKind::kKwExpect, Subclause("16.17"));
  Stmt* stmt = ParseProceduralPropertySpec(StmtKind::kExpect, loc,
                                           Subclause("16.17"), false);
  ParserAssertHelpers::ParseActionBlock(*this, stmt->assert_pass_stmt,
                                        stmt->assert_fail_stmt);
  stmt->range.end = CurrentLoc();
  return stmt;
}

Stmt* Parser::ParseWaitOrderStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWaitOrder, Subclause("15.5.4"));
  Expect(TokenKind::kLParen, Subclause("15.5.4"));

  stmt->wait_order_events.push_back(ParseWaitOrderOperand());
  while (Match(TokenKind::kComma)) {
    stmt->wait_order_events.push_back(ParseWaitOrderOperand());
  }
  Expect(TokenKind::kRParen, Subclause("15.5.4"));
  ParserAssertHelpers::ParseActionBlock(*this, stmt->then_branch,
                                        stmt->else_branch);
  return stmt;
}

}  // namespace delta
