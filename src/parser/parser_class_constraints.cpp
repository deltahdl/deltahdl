#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_constraint_items_internal.h"

namespace delta {

void Parser::CaptureSoftConstraintRelation(ClassMember* member) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Consume();
  auto after_soft = lexer_.SavePos();
  if (!TryCaptureDist(member, true)) {
    lexer_.RestorePos(after_soft);
    Expr* rel = ParseExpr();
    if (rel != nullptr && Check(TokenKind::kSemicolon) && member) {
      member->constraint_soft_exprs.push_back(rel);
    }
  }
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
}

void Parser::CaptureConstraintRelation(ClassMember* member) {
  TokenKind k = CurrentToken().kind;
  if (k == TokenKind::kKwSoft) {
    CaptureSoftConstraintRelation(member);
    return;
  }
  if (k == TokenKind::kKwUnique) {
    auto saved = lexer_.SavePos();
    diag_.PushSuppress();
    TryCaptureUnique(member);
    diag_.PopSuppress();
    lexer_.RestorePos(saved);
    return;
  }
  if (k == TokenKind::kKwForeach || k == TokenKind::kKwSolve ||
      k == TokenKind::kKwDist || k == TokenKind::kKwDisable ||
      k == TokenKind::kLBrace || k == TokenKind::kRBrace ||
      k == TokenKind::kSemicolon) {
    return;
  }
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  bool captured = k == TokenKind::kKwIf ? TryCaptureIfElseConstraint(member)
                                        : TryCaptureBracedImplication(member);
  if (!captured && k != TokenKind::kKwIf) {
    lexer_.RestorePos(saved);
    captured = TryCaptureDist(member);
  }
  if (!captured) {
    lexer_.RestorePos(saved);
    Expr* rel = ParseExpr();
    if (rel != nullptr && Check(TokenKind::kSemicolon) && member) {
      member->constraint_exprs.push_back(rel);
    }
  }
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
}

void Parser::CaptureDisableSoftConstraint(ClassMember* member) {
  Consume();
  if (!Match(TokenKind::kKwSoft)) return;
  if (Check(TokenKind::kIdentifier)) {
    Token id = CurrentToken();
    Consume();
    std::string_view name = id.text;
    if (Match(TokenKind::kDot) && CurrentToken().text == "size") {
      Consume();
      if (Match(TokenKind::kLParen)) Match(TokenKind::kRParen);
      const std::string kKey = std::string(id.text) + ".size";
      name = {arena_.AllocString(kKey.data(), kKey.size()), kKey.size()};
    }
    if (Check(TokenKind::kSemicolon) && member != nullptr) {
      ConstraintSoftVarRef ref;
      ref.name = name;
      ref.loc = id.loc;
      member->constraint_disable_soft_refs.push_back(ref);
    }
  }
  while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
         !Check(TokenKind::kRBrace)) {
    Consume();
  }
}

struct Parser::ImpliedRelation {
  Expr* impl;
  bool soft;
};

Expr* Parser::ParseImpliedRelation(Expr* antecedent, bool& soft) {
  soft = Match(TokenKind::kKwSoft);
  Expr* consequent = ParseExpr();
  if (consequent == nullptr || !Check(TokenKind::kSemicolon)) return nullptr;
  Consume();
  Expr* impl = arena_.Create<Expr>();
  impl->kind = ExprKind::kBinary;
  impl->op = TokenKind::kArrow;
  impl->lhs = antecedent;
  impl->rhs = consequent;
  impl->range.start = antecedent->range.start;
  impl->range.end = consequent->range.end;
  return impl;
}

bool Parser::ParseImpliedSet(Expr* antecedent,
                             std::vector<ImpliedRelation>& out) {
  if (!Match(TokenKind::kLBrace)) return false;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    bool soft = false;
    Expr* impl = ParseImpliedRelation(antecedent, soft);
    if (impl == nullptr) return false;
    out.push_back({impl, soft});
  }
  Consume();
  return true;
}

bool Parser::TryCaptureBracedImplication(ClassMember* member) {
  Expr* antecedent = ParseExprBp(3);
  if (antecedent == nullptr || !Check(TokenKind::kArrow)) return false;
  Consume();
  std::vector<ImpliedRelation> synthesized;
  if (Check(TokenKind::kKwSoft)) {
    bool soft = false;
    Expr* impl = ParseImpliedRelation(antecedent, soft);
    if (impl == nullptr) return false;
    synthesized.push_back({impl, soft});
  } else if (!ParseImpliedSet(antecedent, synthesized)) {
    return false;
  }
  if (member == nullptr) return true;
  for (const ImpliedRelation& r : synthesized) {
    std::vector<Expr*>& into =
        r.soft ? member->constraint_soft_exprs : member->constraint_exprs;
    into.push_back(r.impl);
  }
  return true;
}

bool Parser::ParseDistWeight(ConstraintDistItem& item) {
  if (MatchColonSlash()) {
    item.per_element = false;
    item.weight = ParseExpr();
    return item.weight != nullptr;
  }
  if (Check(TokenKind::kColon)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kEq)) {
      Consume();
      item.per_element = true;
      item.weight = ParseExpr();
      return item.weight != nullptr;
    }
    lexer_.RestorePos(saved);
  }
  return false;
}

bool Parser::ParseDistRange(ConstraintDistItem& item) {
  item.lo = ParseExpr();
  if (item.lo == nullptr) return false;
  if (Check(TokenKind::kPlusSlashMinus) ||
      Check(TokenKind::kPlusPercentMinus)) {
    item.tolerance_relative = Check(TokenKind::kPlusPercentMinus);
    Consume();
    item.tolerance = ParseExpr();
    if (item.tolerance == nullptr) return false;
  } else {
    if (!Match(TokenKind::kColon)) return false;
    item.hi = ParseExpr();
    if (item.hi == nullptr) return false;
  }
  return Match(TokenKind::kRBracket);
}

bool Parser::ParseDistItem(ConstraintDistItem& item) {
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
    return ParseDistWeight(item);
  }
  if (Match(TokenKind::kLBracket)) {
    item.is_range = true;
    if (!ParseDistRange(item)) return false;
    if (!ParseDistWeight(item)) item.per_element = true;
    return true;
  }
  item.value = ParseExpr();
  if (item.value == nullptr) return false;
  ParseDistWeight(item);
  return true;
}

bool Parser::TryCaptureDist(ClassMember* member, bool is_soft) {
  Expr* target = ParseExpr();
  if (target == nullptr || !Check(TokenKind::kKwDist)) return false;
  Consume();
  if (!Check(TokenKind::kLBrace)) return false;
  Consume();
  ConstraintDistRef ref;
  ref.target = target;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    ConstraintDistItem item;
    if (!ParseDistItem(item)) return false;
    ref.items.push_back(item);
    if (!Check(TokenKind::kRBrace) && !Match(TokenKind::kComma)) return false;
  }
  Consume();
  if (member) {
    if (is_soft)
      member->constraint_soft_dist_refs.push_back(ref);
    else
      member->constraint_dist_refs.push_back(ref);
  }
  return true;
}

bool Parser::TryCaptureUnique(ClassMember* member) {
  if (!Check(TokenKind::kKwUnique)) return false;
  Consume();
  if (!Check(TokenKind::kLBrace)) return false;
  Consume();
  std::vector<Expr*> members;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    Expr* item = ParseExpr();
    if (item == nullptr) return false;
    members.push_back(item);
    if (!Check(TokenKind::kRBrace) && !Match(TokenKind::kComma)) return false;
  }
  Consume();
  if (member) member->constraint_unique_refs.push_back(std::move(members));
  return true;
}

Expr* Parser::MakeConstraintImplication(Expr* guard, Expr* consequent) {
  if (guard == nullptr) return consequent;
  Expr* impl = arena_.Create<Expr>();
  impl->kind = ExprKind::kBinary;
  impl->op = TokenKind::kArrow;
  impl->lhs = guard;
  impl->rhs = consequent;
  impl->range.start = guard->range.start;
  impl->range.end = consequent->range.end;
  return impl;
}

Expr* Parser::MakeConstraintAnd(Expr* lhs, Expr* rhs) {
  Expr* conj = arena_.Create<Expr>();
  conj->kind = ExprKind::kBinary;
  conj->op = TokenKind::kAmpAmp;
  conj->lhs = lhs;
  conj->rhs = rhs;
  conj->range.start = lhs->range.start;
  conj->range.end = rhs->range.end;
  return conj;
}

Expr* Parser::MakeConstraintNot(Expr* operand) {
  Expr* neg = arena_.Create<Expr>();
  neg->kind = ExprKind::kUnary;
  neg->op = TokenKind::kBang;
  neg->lhs = operand;
  neg->range = operand->range;
  return neg;
}

bool Parser::CaptureGuardedConstraintItem(Expr* guard,
                                          std::vector<Expr*>& out) {
  if (Check(TokenKind::kKwIf)) return CaptureGuardedIf(guard, out);
  Expr* rel = ParseExpr();
  if (rel == nullptr || !Check(TokenKind::kSemicolon)) return false;
  Consume();
  out.push_back(MakeConstraintImplication(guard, rel));
  return true;
}

bool Parser::CaptureGuardedConstraintSet(Expr* guard, std::vector<Expr*>& out) {
  if (Check(TokenKind::kLBrace)) {
    Consume();
    while (!Check(TokenKind::kRBrace)) {
      if (AtEnd()) return false;
      if (!CaptureGuardedConstraintItem(guard, out)) return false;
    }
    Consume();
    return true;
  }
  return CaptureGuardedConstraintItem(guard, out);
}

bool Parser::CaptureGuardedIf(Expr* guard, std::vector<Expr*>& out) {
  Consume();
  if (!Check(TokenKind::kLParen)) return false;
  Consume();
  Expr* cond = ParseExpr();
  if (cond == nullptr || !Check(TokenKind::kRParen)) return false;
  Consume();
  Expr* then_guard = guard ? MakeConstraintAnd(guard, cond) : cond;
  if (!CaptureGuardedConstraintSet(then_guard, out)) return false;
  if (Check(TokenKind::kKwElse)) {
    Consume();
    Expr* neg = MakeConstraintNot(cond);
    Expr* else_guard = guard ? MakeConstraintAnd(guard, neg) : neg;
    if (!CaptureGuardedConstraintSet(else_guard, out)) return false;
  }
  return true;
}

bool Parser::TryCaptureIfElseConstraint(ClassMember* member) {
  std::vector<Expr*> out;
  if (!CaptureGuardedIf(nullptr, out)) return false;
  if (member) {
    for (Expr* impl : out) member->constraint_exprs.push_back(impl);
  }
  return true;
}

void Parser::ScanConstraintBodyRelations(ClassMember* member,
                                         bool inline_block) {
  if (!inline_block) ParserConstraintItemHelpers::ReportLocalQualifiers(*this);
  ++constraint_block_depth_;
  ParserConstraintItemHelpers::Capture(*this, member);
  int depth = 1;
  bool prev_was_qualifier = false;
  bool in_soft = false;
  bool at_relation_start = true;
  while (depth > 0 && !AtEnd()) {
    if (at_relation_start && depth == 1 && !in_soft) {
      CaptureConstraintRelation(member);
    }
    bool starts_with_semicolon = Check(TokenKind::kSemicolon);
    bool carried_qualifier = prev_was_qualifier;
    prev_was_qualifier =
        ScanConstraintBodyToken(member, depth, in_soft, carried_qualifier);
    at_relation_start = starts_with_semicolon;
  }
  --constraint_block_depth_;
}

static void ReportBlockQualifier(const ClassMember& m, const char* keyword,
                                 DiagEngine& diag) {
  diag.Error(m.loc,
             std::string("'") + keyword +
                 "' is no qualifier of a constraint written with a block",
             Subclause("A.1.10"));
}

static void RejectConstraintQualifiers(ClassMember* m, DiagEngine& diag) {
  if (!m->is_constraint_prototype) {
    if (m->is_constraint_extern) ReportBlockQualifier(*m, "extern", diag);
    if (m->is_pure_virtual) ReportBlockQualifier(*m, "pure", diag);
    m->is_constraint_extern = false;
    m->is_pure_virtual = false;
    return;
  }
  if (m->is_constraint_extern && m->is_pure_virtual) {
    diag.Error(m->loc,
               "a constraint prototype takes 'extern' or 'pure', not both",
               Subclause("A.1.10"));
  } else if (m->is_static &&
             (m->extern_follows_qualifier || m->pure_follows_qualifier)) {
    diag.Error(m->loc,
               "a constraint prototype's 'static' is written before its "
               "'extern' or 'pure'",
               Subclause("A.1.10"));
  }
}

ClassMember* Parser::ParseConstraintStub(ClassMember* member) {
  member->kind = ClassMemberKind::kConstraint;
  Consume();

  const bool kPrototype = ParseConstraintHeader(member);
  RejectConstraintQualifiers(member, diag_);
  if (kPrototype) return member;

  ScanConstraintBodyRelations(member, false);
  return member;
}

bool Parser::CheckDistDefault(SourceLoc loc, int& default_count) {
  if (++default_count > 1) {
    diag_.Error(loc,
                "this distribution already has a default specification; it "
                "can have only one",
                Subclause("18.5.3"));
  }
  if (CheckColonSlash()) return true;
  diag_.Error(loc,
              "a distribution's default specification takes its weight "
              "through :/ and nothing else",
              Subclause("18.5.3"));
  return false;
}

void Parser::CheckDistSet() {
  if (!Match(TokenKind::kLBrace)) return;
  int depth = 1;
  int default_count = 0;
  while (depth > 0 && !AtEnd()) {
    if (Check(TokenKind::kKwDefault)) {
      Token def = Consume();
      if (CheckDistDefault(def.loc, default_count)) MatchColonSlash();
    } else if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      CheckConstraintExprToken(CurrentToken());
      Consume();
    }
  }
}

static bool LiteralHasFourStateDigit(std::string_view text) {
  for (char c : text) {
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

namespace {

struct ForeachBracketScan {
  int bracket_depth;
  int slot;
  int loop_var_count;
  std::vector<std::string_view> loop_vars;
};

void HandleForeachBracketToken(DiagEngine& diag, const Token& t,
                               std::string_view array_name,
                               ForeachBracketScan& scan) {
  if (t.kind == TokenKind::kLBracket) {
    ++scan.bracket_depth;
    return;
  }
  if (t.kind == TokenKind::kRBracket) {
    --scan.bracket_depth;
    return;
  }
  if (scan.bracket_depth == 1 && t.kind == TokenKind::kComma) {
    ++scan.slot;
    return;
  }
  if (scan.bracket_depth == 1 && t.kind == TokenKind::kIdentifier) {
    scan.loop_var_count = scan.slot;
    scan.loop_vars.resize(static_cast<size_t>(scan.slot));
    scan.loop_vars.back() = t.text;
    if (!array_name.empty() && t.text == array_name) {
      diag.Error(t.loc,
                 std::string("foreach loop variable '") + std::string(t.text) +
                     "' may not have the same name as the array it "
                     "iterates over",
                 Subclause("18.5.7.1"));
    }
  }
}

void RecordForeachConstraintRef(ClassMember* member,
                                std::string_view array_name,
                                const ForeachBracketScan& scan,
                                std::vector<Expr*> body,
                                SourceLoc foreach_loc) {
  if (member && !array_name.empty()) {
    ConstraintForeachRef ref;
    ref.array_name = array_name;
    ref.loop_var_count = scan.loop_var_count;
    ref.loop_vars = scan.loop_vars;
    ref.body = std::move(body);
    ref.loc = foreach_loc;
    member->constraint_foreach_refs.push_back(ref);
  }
}

}  // namespace

void Parser::CaptureForeachConstraintBody(std::vector<Expr*>& body) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  std::vector<Expr*> items;
  bool complete = true;
  if (Match(TokenKind::kLBrace)) {
    while (!Check(TokenKind::kRBrace) && !AtEnd()) {
      Expr* rel = ParseExpr();
      if (rel == nullptr || !Match(TokenKind::kSemicolon)) {
        complete = false;
        break;
      }
      items.push_back(rel);
    }
  } else {
    Expr* rel = ParseExpr();
    complete = rel != nullptr && Check(TokenKind::kSemicolon);
    if (complete) items.push_back(rel);
  }
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (complete) body = std::move(items);
}

void Parser::CheckForeachConstraintHeader(ClassMember* member) {
  SourceLoc foreach_loc = CurrentLoc();
  Consume();
  if (!Match(TokenKind::kLParen)) return;
  std::string_view array_name;
  while (!Check(TokenKind::kLBracket) && !Check(TokenKind::kRParen) &&
         !AtEnd()) {
    Token t = Consume();
    if (t.kind == TokenKind::kIdentifier) {
      array_name = t.text;
    } else if (t.kind == TokenKind::kLParen) {
      diag_.Error(
          t.loc,
          "a function call may not stand in for the array identifier of "
          "a foreach iterative constraint",
          Subclause("18.5.7.1"));
    }
  }
  ForeachBracketScan scan{0, 0, 0, {}};
  if (Match(TokenKind::kLBracket)) {
    scan.slot = 1;
    scan.bracket_depth = 1;
    while (scan.bracket_depth > 0 && !AtEnd()) {
      Token t = Consume();
      HandleForeachBracketToken(diag_, t, array_name, scan);
    }
  }
  Match(TokenKind::kRParen);
  std::vector<Expr*> body;
  CaptureForeachConstraintBody(body);
  RecordForeachConstraintRef(member, array_name, scan, std::move(body),
                             foreach_loc);
}

namespace {

struct SolveBeforeEntryScan {
  ConstraintSolveBeforeEntry entry;
  bool qualified = false;
  bool method = false;
  bool dotted = true;
};

void ScanSolveBeforeToken(const Token& t, SolveBeforeEntryScan& scan) {
  switch (t.kind) {
    case TokenKind::kIdentifier:
      if (!scan.entry.name.empty())
        scan.entry.handles.push_back(scan.entry.name);
      scan.entry.name = t.text;
      break;
    case TokenKind::kDot:
      scan.qualified = true;
      break;
    case TokenKind::kColonColon:
      scan.qualified = true;
      scan.dotted = false;
      break;
    case TokenKind::kLParen:
      scan.method = true;
      scan.dotted = false;
      break;
    default:
      scan.dotted = false;
      break;
  }
}

}  // namespace

void Parser::ParseSolveBeforeList(
    std::vector<ConstraintSolveBeforeEntry>& out) {
  while (!AtEnd()) {
    SolveBeforeEntryScan scan;
    while (!Check(TokenKind::kComma) && !Check(TokenKind::kKwBefore) &&
           !Check(TokenKind::kSemicolon) && !Check(TokenKind::kRBrace) &&
           !AtEnd()) {
      ScanSolveBeforeToken(Consume(), scan);
    }
    scan.entry.is_simple = !scan.qualified && !scan.method;
    if (!scan.dotted) scan.entry.handles.clear();
    if (!scan.entry.name.empty()) out.push_back(scan.entry);
    if (!Match(TokenKind::kComma)) break;
  }
}

void Parser::CheckSolveBeforeConstraint(ClassMember* member) {
  ConstraintSolveBeforeRef ref;
  ref.loc = CurrentLoc();
  Consume();
  ParseSolveBeforeList(ref.before);
  if (!Match(TokenKind::kKwBefore)) return;
  ParseSolveBeforeList(ref.after);
  Match(TokenKind::kSemicolon);
  if (member) member->constraint_solve_before_refs.push_back(std::move(ref));
}

void Parser::CheckConstraintExprToken(const Token& tok) {
  switch (tok.kind) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
      diag_.Error(tok.loc,
                  "4-state equality operator is not allowed in a constraint",
                  Subclause("18.3"));
      break;
    case TokenKind::kPlusPlus:
    case TokenKind::kMinusMinus:
      diag_.Error(tok.loc,
                  "operator with side effects is not allowed in a constraint",
                  Subclause("18.5"));
      break;
    case TokenKind::kIntLiteral:
    case TokenKind::kUnbasedUnsizedLiteral:
      if (LiteralHasFourStateDigit(tok.text)) {
        diag_.Error(tok.loc, "4-state value is not allowed in a constraint",
                    Subclause("18.3"));
      }
      break;
    default:
      break;
  }
}

}  // namespace delta
