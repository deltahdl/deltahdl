#include "parser/parser.h"

namespace delta {

// Pratt parser: binding powers for SystemVerilog operators (IEEE 1800-2023 §11)
// Higher binding power = tighter binding

struct BpPair {
  int left;
  int right;
};

static BpPair infix_bp(TokenKind kind) {
  switch (kind) {
    case TokenKind::PipeDashGt:
    case TokenKind::PipeEqGt:
      return {1, 2};
    case TokenKind::PipePipe:
      return {3, 4};
    case TokenKind::AmpAmp:
      return {5, 6};
    case TokenKind::Pipe:
      return {7, 8};
    case TokenKind::Caret:
    case TokenKind::CaretTilde:
    case TokenKind::TildeCaret:
      return {9, 10};
    case TokenKind::Amp:
      return {11, 12};
    case TokenKind::EqEq:
    case TokenKind::BangEq:
    case TokenKind::EqEqEq:
    case TokenKind::BangEqEq:
    case TokenKind::EqEqQuestion:
    case TokenKind::BangEqQuestion:
      return {13, 14};
    case TokenKind::Lt:
    case TokenKind::Gt:
    case TokenKind::LtEq:
    case TokenKind::GtEq:
      return {15, 16};
    case TokenKind::LtLt:
    case TokenKind::GtGt:
    case TokenKind::LtLtLt:
    case TokenKind::GtGtGt:
      return {17, 18};
    case TokenKind::Plus:
    case TokenKind::Minus:
      return {19, 20};
    case TokenKind::Star:
    case TokenKind::Slash:
    case TokenKind::Percent:
      return {21, 22};
    case TokenKind::Power:
      return {24, 23};  // right-assoc
    default:
      return {-1, -1};
  }
}

static int prefix_bp(TokenKind kind) {
  switch (kind) {
    case TokenKind::Plus:
    case TokenKind::Minus:
    case TokenKind::Bang:
    case TokenKind::Tilde:
    case TokenKind::Amp:
    case TokenKind::TildeAmp:
    case TokenKind::Pipe:
    case TokenKind::TildePipe:
    case TokenKind::Caret:
    case TokenKind::TildeCaret:
    case TokenKind::CaretTilde:
      return 25;
    default:
      return -1;
  }
}

Expr* Parser::parse_expr() { return parse_expr_bp(0); }

Expr* Parser::parse_expr_bp(int min_bp) {
  auto* lhs = parse_prefix_expr();

  while (true) {
    auto tok = current_token();
    if (tok.is_eof()) {
      break;
    }

    // Ternary: expr ? expr : expr
    if (tok.kind == TokenKind::Question && min_bp <= 1) {
      consume();
      auto* tern = arena_.create<Expr>();
      tern->kind = ExprKind::Ternary;
      tern->condition = lhs;
      tern->true_expr = parse_expr_bp(0);
      expect(TokenKind::Colon);
      tern->false_expr = parse_expr_bp(0);
      lhs = tern;
      continue;
    }

    auto [lbp, rbp] = infix_bp(tok.kind);
    if (lbp < 0 || lbp < min_bp) {
      break;
    }

    auto op = consume();
    auto* rhs = parse_expr_bp(rbp);
    auto* bin = arena_.create<Expr>();
    bin->kind = ExprKind::Binary;
    bin->op = op.kind;
    bin->lhs = lhs;
    bin->rhs = rhs;
    bin->range.start = lhs->range.start;
    lhs = bin;
  }
  return lhs;
}

Expr* Parser::parse_prefix_expr() {
  auto tok = current_token();
  int bp = prefix_bp(tok.kind);
  if (bp >= 0) {
    auto op = consume();
    auto* operand = parse_expr_bp(bp);
    auto* unary = arena_.create<Expr>();
    unary->kind = ExprKind::Unary;
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }
  return parse_primary_expr();
}

Expr* Parser::make_literal(ExprKind kind, const Token& tok) {
  consume();
  auto* lit = arena_.create<Expr>();
  lit->kind = kind;
  lit->text = tok.text;
  lit->range.start = tok.loc;
  return lit;
}

Expr* Parser::parse_primary_expr() {
  auto tok = current_token();

  if (tok.kind == TokenKind::IntLiteral ||
      tok.kind == TokenKind::UnbasedUnsizedLiteral) {
    return make_literal(ExprKind::IntegerLiteral, tok);
  }

  if (tok.kind == TokenKind::RealLiteral) {
    return make_literal(ExprKind::RealLiteral, tok);
  }

  if (tok.kind == TokenKind::StringLiteral) {
    return make_literal(ExprKind::StringLiteral, tok);
  }

  if (tok.kind == TokenKind::SystemIdentifier) {
    return parse_system_call();
  }

  if (tok.kind == TokenKind::Identifier) {
    consume();
    auto* id = arena_.create<Expr>();
    id->kind = ExprKind::Identifier;
    id->text = tok.text;
    id->range.start = tok.loc;

    if (check(TokenKind::LParen)) return parse_call_expr(id);
    if (check(TokenKind::LBracket)) return parse_select_expr(id);
    return id;
  }

  if (tok.kind == TokenKind::LParen) {
    consume();
    auto* expr = parse_expr();
    expect(TokenKind::RParen);
    return expr;
  }

  if (tok.kind == TokenKind::LBrace) {
    return parse_concatenation();
  }

  diag_.error(tok.loc, "expected expression");
  consume();
  auto* err = arena_.create<Expr>();
  err->kind = ExprKind::IntegerLiteral;
  err->range.start = tok.loc;
  return err;
}

Expr* Parser::parse_call_expr(Expr* callee) {
  expect(TokenKind::LParen);
  auto* call = arena_.create<Expr>();
  call->kind = ExprKind::Call;
  call->callee = callee->text;
  call->range.start = callee->range.start;
  if (!check(TokenKind::RParen)) {
    call->args.push_back(parse_expr());
    while (match(TokenKind::Comma)) {
      call->args.push_back(parse_expr());
    }
  }
  expect(TokenKind::RParen);
  return call;
}

Expr* Parser::parse_select_expr(Expr* base) {
  consume();  // LBracket
  auto* sel = arena_.create<Expr>();
  sel->kind = ExprKind::Select;
  sel->base = base;
  sel->index = parse_expr();
  if (match(TokenKind::Colon)) {
    sel->index_end = parse_expr();
  }
  expect(TokenKind::RBracket);
  return sel;
}

Expr* Parser::parse_system_call() {
  auto tok = consume();
  auto* call = arena_.create<Expr>();
  call->kind = ExprKind::SystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!match(TokenKind::LParen)) return call;
  if (!check(TokenKind::RParen)) {
    call->args.push_back(parse_expr());
    while (match(TokenKind::Comma)) {
      call->args.push_back(parse_expr());
    }
  }
  expect(TokenKind::RParen);
  return call;
}

Expr* Parser::parse_concatenation() {
  auto loc = current_loc();
  expect(TokenKind::LBrace);
  auto* first = parse_expr();

  // Replication: {count{elements}}
  if (check(TokenKind::LBrace)) {
    consume();
    auto* rep = arena_.create<Expr>();
    rep->kind = ExprKind::Replicate;
    rep->repeat_count = first;
    rep->range.start = loc;
    rep->elements.push_back(parse_expr());
    while (match(TokenKind::Comma)) {
      rep->elements.push_back(parse_expr());
    }
    expect(TokenKind::RBrace);
    expect(TokenKind::RBrace);
    return rep;
  }

  auto* cat = arena_.create<Expr>();
  cat->kind = ExprKind::Concatenation;
  cat->range.start = loc;
  cat->elements.push_back(first);
  while (match(TokenKind::Comma)) {
    cat->elements.push_back(parse_expr());
  }
  expect(TokenKind::RBrace);
  return cat;
}

}  // namespace delta
