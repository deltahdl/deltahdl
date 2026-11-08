#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/specify_internal.h"

namespace delta {

namespace {

std::string_view SpecifyConditionOperator(TokenKind op) {
  switch (op) {
    case TokenKind::kBang:
      return "!";
    case TokenKind::kTilde:
      return "~";
    case TokenKind::kAmpAmp:
      return "&&";
    case TokenKind::kPipePipe:
      return "||";
    case TokenKind::kEqEq:
      return "==";
    case TokenKind::kBangEq:
      return "!=";
    case TokenKind::kEqEqEq:
      return "===";
    case TokenKind::kBangEqEq:
      return "!==";
    case TokenKind::kAmp:
      return "&";
    case TokenKind::kPipe:
      return "|";
    case TokenKind::kCaret:
      return "^";
    case TokenKind::kCaretTilde:
      return "^~";
    case TokenKind::kTildeCaret:
      return "~^";
    case TokenKind::kTildeAmp:
      return "~&";
    case TokenKind::kTildePipe:
      return "~|";
    default:
      return {};
  }
}

std::string SpecifyConditionIndexText(const Expr* index) {
  if (index == nullptr) return {};
  if (index->kind != ExprKind::kIntegerLiteral) return {};
  return std::to_string(index->int_val);
}

std::string SpecifyConditionSelectText(const Expr* sel) {
  if (sel->is_part_select_plus || sel->is_part_select_minus) return {};
  std::string base = SpecifyConditionText(sel->base);
  std::string index = SpecifyConditionIndexText(sel->index);
  if (base.empty() || index.empty()) return {};
  if (sel->index_end == nullptr) return base + "[" + index + "]";
  std::string index_end = SpecifyConditionIndexText(sel->index_end);
  if (index_end.empty()) return {};
  return base + "[" + index + ":" + index_end + "]";
}

std::string SpecifyConditionConcatText(const Expr* cat) {
  if (cat->elements.empty()) return {};
  std::string out = "{";
  for (std::size_t i = 0; i < cat->elements.size(); ++i) {
    std::string element = SpecifyConditionText(cat->elements[i]);
    if (element.empty()) return {};
    if (i != 0) out += ", ";
    out += element;
  }
  return out + "}";
}

std::string SpecifyConditionReplicateText(const Expr* rep) {
  std::string count = SpecifyConditionIndexText(rep->repeat_count);
  std::string body = SpecifyConditionConcatText(rep);
  if (count.empty() || body.empty()) return {};
  return "{" + count + body + "}";
}

std::string SpecifyConditionTernaryText(const Expr* cond) {
  std::string test = SpecifyConditionText(cond->condition);
  std::string on_true = SpecifyConditionText(cond->true_expr);
  std::string on_false = SpecifyConditionText(cond->false_expr);
  if (test.empty() || on_true.empty() || on_false.empty()) return {};
  return test + " ? " + on_true + " : " + on_false;
}

}  // namespace

std::string SpecifyConditionText(const Expr* cond) {
  if (cond == nullptr) return {};
  switch (cond->kind) {
    case ExprKind::kIdentifier:
      return std::string(cond->text);
    case ExprKind::kIntegerLiteral:
      return std::to_string(cond->int_val);
    case ExprKind::kUnary: {
      std::string_view op = SpecifyConditionOperator(cond->op);
      std::string operand = SpecifyConditionText(cond->lhs);
      if (op.empty() || operand.empty()) return {};
      return std::string(op) + operand;
    }
    case ExprKind::kBinary: {
      std::string_view op = SpecifyConditionOperator(cond->op);
      std::string lhs = SpecifyConditionText(cond->lhs);
      std::string rhs = SpecifyConditionText(cond->rhs);
      if (op.empty() || lhs.empty() || rhs.empty()) return {};
      return lhs + " " + std::string(op) + " " + rhs;
    }
    case ExprKind::kSelect:
      return SpecifyConditionSelectText(cond);
    case ExprKind::kConcatenation:
      return SpecifyConditionConcatText(cond);
    case ExprKind::kReplicate:
      return SpecifyConditionReplicateText(cond);
    case ExprKind::kTernary:
      return SpecifyConditionTernaryText(cond);
    default:
      return {};
  }
}

namespace {

void SkipSpecifyConditionSpace(std::string_view s, std::size_t& pos) {
  while (pos < s.size() &&
         std::isspace(static_cast<unsigned char>(s[pos])) != 0) {
    ++pos;
  }
}

}  // namespace

bool SpecifyConditionsMatch(std::string_view a, std::string_view b) {
  std::size_t i = 0;
  std::size_t j = 0;
  SkipSpecifyConditionSpace(a, i);
  SkipSpecifyConditionSpace(b, j);
  while (i < a.size() && j < b.size()) {
    if (a[i] != b[j]) return false;
    ++i;
    ++j;
    SkipSpecifyConditionSpace(a, i);
    SkipSpecifyConditionSpace(b, j);
  }
  return i == a.size() && j == b.size();
}

}  // namespace delta
