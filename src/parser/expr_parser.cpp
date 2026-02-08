#include <charconv>
#include <cstdlib>

#include "parser/parser.h"

namespace delta {

// Parse a SystemVerilog integer literal text into a uint64_t value.
// Handles: decimal "42", based "8'hFF", underscore "1_000".
static uint64_t ParseIntText(std::string_view text) {
  // Strip underscores into a local buffer.
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }

  // Find tick for based literals (e.g., 8'hFF).
  auto tick = buf.find('\'');
  if (tick == std::string::npos) {
    uint64_t val = 0;
    std::from_chars(buf.data(), buf.data() + buf.size(), val, 10);
    return val;
  }

  // Skip optional 's' after tick, then parse base letter.
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  int base = 10;
  if (i < buf.size()) {
    switch (buf[i]) {
      case 'h':
      case 'H':
        base = 16;
        break;
      case 'b':
      case 'B':
        base = 2;
        break;
      case 'o':
      case 'O':
        base = 8;
        break;
      default:
        break;
    }
    ++i;
  }
  uint64_t val = 0;
  std::from_chars(buf.data() + i, buf.data() + buf.size(), val, base);
  return val;
}

// Parse a SystemVerilog real or time literal text into a double value.
// Handles: fixed "3.14", exponent "1e10", underscore "1_000.5".
// For time literals (e.g., "100ns"), strtod stops at the suffix.
static double ParseRealText(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }
  return std::strtod(buf.c_str(), nullptr);
}

// Pratt parser: binding powers for SystemVerilog operators (IEEE 1800-2023 §11)
// Higher binding power = tighter binding

static std::pair<int, int> InfixBp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPipeDashGt:
    case TokenKind::kPipeEqGt:
      return {1, 2};
    case TokenKind::kPipePipe:
      return {3, 4};
    case TokenKind::kAmpAmp:
      return {5, 6};
    case TokenKind::kPipe:
      return {7, 8};
    case TokenKind::kCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kTildeCaret:
      return {9, 10};
    case TokenKind::kAmp:
      return {11, 12};
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
      return {13, 14};
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
      return {15, 16};
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return {17, 18};
    case TokenKind::kPlus:
    case TokenKind::kMinus:
      return {19, 20};
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      return {21, 22};
    case TokenKind::kPower:
      return {24, 23};  // right-assoc
    default:
      return {-1, -1};
  }
}

static int PrefixBp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kBang:
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return 25;
    default:
      return -1;
  }
}

Expr* Parser::ParseExpr() { return ParseExprBp(0); }

Expr* Parser::ParseExprBp(int min_bp) {
  auto* lhs = ParsePrefixExpr();
  return ParseInfixBp(lhs, min_bp);
}

Expr* Parser::ParseInfixBp(Expr* lhs, int min_bp) {
  while (true) {
    auto tok = CurrentToken();
    if (tok.IsEof()) {
      break;
    }

    // Ternary: expr ? expr : expr
    if (tok.kind == TokenKind::kQuestion && min_bp <= 1) {
      Consume();
      auto* tern = arena_.Create<Expr>();
      tern->kind = ExprKind::kTernary;
      tern->condition = lhs;
      tern->true_expr = ParseExprBp(0);
      Expect(TokenKind::kColon);
      tern->false_expr = ParseExprBp(0);
      lhs = tern;
      continue;
    }

    auto [lbp, rbp] = InfixBp(tok.kind);
    if (lbp < 0 || lbp < min_bp) {
      break;
    }

    auto op = Consume();
    auto* rhs = ParseExprBp(rbp);
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op.kind;
    bin->lhs = lhs;
    bin->rhs = rhs;
    bin->range.start = lhs->range.start;
    lhs = bin;
  }
  return lhs;
}

Expr* Parser::ParsePrefixExpr() {
  auto tok = CurrentToken();
  int bp = PrefixBp(tok.kind);
  if (bp >= 0) {
    auto op = Consume();
    auto* operand = ParseExprBp(bp);
    auto* unary = arena_.Create<Expr>();
    unary->kind = ExprKind::kUnary;
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }
  return ParsePrimaryExpr();
}

Expr* Parser::MakeLiteral(ExprKind kind, const Token& tok) {
  Consume();
  auto* lit = arena_.Create<Expr>();
  lit->kind = kind;
  lit->text = tok.text;
  lit->range.start = tok.loc;
  if (kind == ExprKind::kIntegerLiteral) {
    lit->int_val = ParseIntText(tok.text);
  } else if (kind == ExprKind::kRealLiteral || kind == ExprKind::kTimeLiteral) {
    lit->real_val = ParseRealText(tok.text);
  }
  return lit;
}

Expr* Parser::ParsePrimaryExpr() {
  auto tok = CurrentToken();

  if (tok.kind == TokenKind::kIntLiteral ||
      tok.kind == TokenKind::kUnbasedUnsizedLiteral) {
    return MakeLiteral(ExprKind::kIntegerLiteral, tok);
  }

  if (tok.kind == TokenKind::kRealLiteral) {
    return MakeLiteral(ExprKind::kRealLiteral, tok);
  }

  if (tok.kind == TokenKind::kTimeLiteral) {
    return MakeLiteral(ExprKind::kTimeLiteral, tok);
  }

  if (tok.kind == TokenKind::kStringLiteral) {
    return MakeLiteral(ExprKind::kStringLiteral, tok);
  }

  if (tok.kind == TokenKind::kSystemIdentifier) {
    return ParseSystemCall();
  }

  if (tok.kind == TokenKind::kIdentifier) {
    Consume();
    auto* id = arena_.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = tok.text;
    id->range.start = tok.loc;

    if (Check(TokenKind::kLParen)) return ParseCallExpr(id);
    if (Check(TokenKind::kLBracket)) return ParseSelectExpr(id);
    return id;
  }

  if (tok.kind == TokenKind::kLParen) {
    Consume();
    auto* expr = ParseExpr();
    Expect(TokenKind::kRParen);
    return expr;
  }

  if (tok.kind == TokenKind::kLBrace) {
    return ParseConcatenation();
  }

  diag_.Error(tok.loc, "expected expression");
  Consume();
  auto* err = arena_.Create<Expr>();
  err->kind = ExprKind::kIntegerLiteral;
  err->range.start = tok.loc;
  return err;
}

Expr* Parser::ParseCallExpr(Expr* callee) {
  Expect(TokenKind::kLParen);
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = callee->text;
  call->range.start = callee->range.start;
  if (!Check(TokenKind::kRParen)) {
    call->args.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      call->args.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen);
  return call;
}

Expr* Parser::ParseSelectExpr(Expr* base) {
  Consume();  // LBracket
  auto* sel = arena_.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = base;
  sel->index = ParseExpr();
  if (Match(TokenKind::kColon)) {
    sel->index_end = ParseExpr();
  }
  Expect(TokenKind::kRBracket);
  return sel;
}

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) return call;
  if (!Check(TokenKind::kRParen)) {
    call->args.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      call->args.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen);
  return call;
}

Expr* Parser::ParseConcatenation() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kLBrace);
  auto* first = ParseExpr();

  // Replication: {count{elements}}
  if (Check(TokenKind::kLBrace)) {
    Consume();
    auto* rep = arena_.Create<Expr>();
    rep->kind = ExprKind::kReplicate;
    rep->repeat_count = first;
    rep->range.start = loc;
    rep->elements.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      rep->elements.push_back(ParseExpr());
    }
    Expect(TokenKind::kRBrace);
    Expect(TokenKind::kRBrace);
    return rep;
  }

  auto* cat = arena_.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->range.start = loc;
  cat->elements.push_back(first);
  while (Match(TokenKind::kComma)) {
    cat->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace);
  return cat;
}

}  // namespace delta
