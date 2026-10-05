#include "simulator/vpi_expr_decompile.h"

#include <algorithm>
#include <cstddef>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/operator_binding_power.h"
#include "simulator/vpi_model_helpers1.h"

namespace delta {

namespace {

// The binding power of an edge no operator beside it can split: either edge
// of a primary, and the left edge of a unary operation.
constexpr int kUnsplit = std::numeric_limits<int>::max();

// §11.4.11 with §11.3.2: the conditional operator binds its condition more
// loosely than every binary operator but the implications, and its last
// operand runs to the end of the expression. These are the powers the parser
// reads it with.
constexpr int kConditionalLeftPower = 1;
constexpr int kConditionalRightPower = 0;

// A rendered expression, with how tightly its text holds together at each
// edge: the loosest binding power among the operators along that edge's spine
// that stand outside parentheses. An operator written next to the text splits
// it there unless that operator binds less tightly.
struct Piece {
  std::string text;
  int left = kUnsplit;
  int right = kUnsplit;
};

std::optional<Piece> Render(const Expr* expr);

// §37.59 detail 2: `operand` written left of an operator that binds it with
// `power`, in parentheses where that operator would otherwise take part of it
// away. Parenthesized, it is whole at both edges.
Piece AsLeftOperand(const Piece& operand, int power) {
  if (power < operand.right) return operand;
  return Piece{VpiDecompileParenthesize(operand.text)};
}

// §37.59 detail 2: `operand` written right of an operator that binds it with
// `power`, in parentheses where it would otherwise not be read whole.
Piece AsRightOperand(const Piece& operand, int power) {
  if (operand.left >= power) return operand;
  return Piece{VpiDecompileParenthesize(operand.text)};
}

// The source spelling of an operator, which TokenKindName gives in quotes.
std::string Spelling(TokenKind kind) {
  const std::string_view kName = TokenKindName(kind);
  if (kName.size() < 3 || kName.front() != '\'') return {};
  return std::string(kName.substr(1, kName.size() - 2));
}

// §11.4: a unary operator before its operand.
std::optional<Piece> RenderUnary(const Expr& expr) {
  const int kPower = PrefixBindingPower(expr.op);
  const std::optional<Piece> kOperand = Render(expr.lhs);
  if (kPower < 0 || !kOperand) return std::nullopt;
  const Piece kInner = AsRightOperand(*kOperand, kPower);
  return Piece{VpiDecompileJoin({Spelling(expr.op), kInner.text}), kUnsplit,
               std::min(kPower, kInner.right)};
}

// §11.4: a binary operator between its operands.
std::optional<Piece> RenderBinary(const Expr& expr) {
  const std::pair<int, int> kPowers = InfixBindingPower(expr.op);
  const std::optional<Piece> kLhs = Render(expr.lhs);
  const std::optional<Piece> kRhs = Render(expr.rhs);
  if (kPowers.first < 0 || !kLhs || !kRhs) return std::nullopt;
  const Piece kLeft = AsLeftOperand(*kLhs, kPowers.first);
  const Piece kRight = AsRightOperand(*kRhs, kPowers.second);
  return Piece{VpiDecompileJoin({kLeft.text, Spelling(expr.op), kRight.text}),
               std::min(kPowers.first, kLeft.left),
               std::min(kPowers.second, kRight.right)};
}

// §11.4.11: the conditional operator, its two operators each one space from
// the operands around them.
std::optional<Piece> RenderConditional(const Expr& expr) {
  const std::optional<Piece> kCondition = Render(expr.condition);
  const std::optional<Piece> kFirst = Render(expr.true_expr);
  const std::optional<Piece> kSecond = Render(expr.false_expr);
  if (!kCondition || !kFirst || !kSecond) return std::nullopt;
  const Piece kTest = AsLeftOperand(*kCondition, kConditionalLeftPower);
  return Piece{
      VpiDecompileJoin({kTest.text, "?", kFirst->text, ":", kSecond->text}),
      std::min(kConditionalLeftPower, kTest.left), kConditionalRightPower};
}

// The expressions of a list, comma separated, `names` naming those of them
// bound by name (§13.5.4). An argument left out (§37.42 detail 8) is nothing
// between its commas. Nothing where one of them cannot be rendered.
std::optional<std::string> RenderList(
    const std::vector<Expr*>& exprs,
    const std::vector<std::string_view>& names) {
  std::string out;
  for (std::size_t i = 0; i < exprs.size(); ++i) {
    if (i > 0) out += ", ";
    const bool kNamed = i < names.size() && !names[i].empty();
    if (kNamed) {
      out += '.';
      out += names[i];
      out += '(';
    }
    if (exprs[i] != nullptr) {
      const std::optional<Piece> kItem = Render(exprs[i]);
      if (!kItem) return std::nullopt;
      out += kItem->text;
    }
    if (kNamed) out += ')';
  }
  return out;
}

std::optional<std::string> RenderConstraintSet(
    const std::vector<ConstraintItem*>& items);

// The text of `expr` alone, nothing where it cannot be rendered.
std::optional<std::string> RenderText(const Expr* expr) {
  const std::optional<Piece> kPiece = Render(expr);
  if (!kPiece) return std::nullopt;
  return kPiece->text;
}

// §18.5.3 with §11.4.13: a dist_item's bracketed range, its two ends or a
// centre and the tolerance about it.
std::optional<std::string> RenderDistRange(const ConstraintDistItem& item) {
  const bool kAboutCentre = item.tolerance != nullptr;
  const std::optional<std::string> kLo = RenderText(item.lo);
  const std::optional<std::string> kEnd =
      RenderText(kAboutCentre ? item.tolerance : item.hi);
  if (!kLo || !kEnd) return std::nullopt;
  std::string_view separator = ":";
  if (kAboutCentre) separator = item.tolerance_relative ? "+%-" : "+/-";
  return "[" + *kLo + std::string(separator) + *kEnd + "]";
}

// §18.5.3: one dist_item, a value, a bracketed range or `default`, with the
// weight it is written with.
std::optional<std::string> RenderDistItem(const ConstraintDistItem& item) {
  std::optional<std::string> text = std::string("default");
  if (item.is_range) {
    text = RenderDistRange(item);
  } else if (!item.is_default) {
    text = RenderText(item.value);
  }
  if (!text || item.weight == nullptr) return text;
  const std::optional<std::string> kWeight = RenderText(item.weight);
  if (!kWeight) return std::nullopt;
  return VpiDecompileJoin({*text, item.per_element ? ":=" : ":/", *kWeight});
}

// §18.5.3: an expression_or_dist, the dist_list braced after `dist`.
std::optional<std::string> RenderExpressionOrDist(const ConstraintItem& item) {
  const std::optional<std::string> kExpr = RenderText(item.expr);
  if (!kExpr || !item.has_dist) return kExpr;
  std::string list;
  for (const ConstraintDistItem& dist_item : item.dist) {
    const std::optional<std::string> kItem = RenderDistItem(dist_item);
    if (!kItem) return std::nullopt;
    if (!list.empty()) list += ", ";
    list += *kItem;
  }
  return VpiDecompileJoin({*kExpr, "dist", "{" + list + "}"});
}

// §18.5.7.1: a foreach's array and its loop variables, a variable left out
// standing as nothing between its commas.
std::optional<std::string> RenderForeachHead(const ConstraintItem& item) {
  const std::optional<std::string> kArray = RenderText(item.expr);
  if (!kArray) return std::nullopt;
  std::string text = *kArray + "[";
  for (std::size_t i = 0; i < item.loop_vars.size(); ++i) {
    if (i > 0) text += ", ";
    text += item.loop_vars[i];
  }
  return VpiDecompileJoin({"foreach", VpiDecompileParenthesize(text + "]")});
}

// §18.5 (A.1.10): an item the source ends with a semicolon, an
// expression_or_dist, a uniqueness constraint, a disable soft or a
// solve-before.
std::optional<std::string> RenderTerminatedItem(const ConstraintItem& item) {
  std::optional<std::string> text;
  switch (item.kind) {
    case ConstraintItemKind::kExpression:
      text = RenderExpressionOrDist(item);
      if (text) text = VpiDecompileJoin({item.soft ? "soft" : "", *text});
      break;
    case ConstraintItemKind::kUnique:
      text = RenderList(item.exprs, {});
      if (text) text = "unique {" + *text + "}";
      break;
    case ConstraintItemKind::kDisableSoft:
      text = RenderText(item.expr);
      if (text) text = VpiDecompileJoin({"disable", "soft", *text});
      break;
    default: {
      const std::optional<std::string> kBefore = RenderList(item.exprs, {});
      const std::optional<std::string> kAfter = RenderList(item.after, {});
      if (kBefore && kAfter) {
        text = VpiDecompileJoin({"solve", *kBefore, "before", *kAfter});
      }
      break;
    }
  }
  if (!text) return std::nullopt;
  return *text + ";";
}

// §18.5.5, §18.5.6 and §18.5.7.1: what an implication, an if-else or a foreach
// writes before the constraint set it governs. An implication's antecedent
// keeps the parentheses that stop the implication taking part of it away.
std::optional<std::string> RenderGoverningHead(const ConstraintItem& item) {
  if (item.kind == ConstraintItemKind::kForeach) return RenderForeachHead(item);
  const std::optional<Piece> kExpr = Render(item.expr);
  if (!kExpr) return std::nullopt;
  if (item.kind == ConstraintItemKind::kIfElse) {
    return VpiDecompileJoin({"if", VpiDecompileParenthesize(kExpr->text)});
  }
  const Piece kAntecedent =
      AsLeftOperand(*kExpr, InfixBindingPower(TokenKind::kArrow).first);
  return VpiDecompileJoin({kAntecedent.text, "->"});
}

// §18.5 (A.1.10): one constraint block item, terminated as the source
// terminates it, or followed by the constraint sets it governs.
std::optional<std::string> RenderConstraintItem(const ConstraintItem& item) {
  if (item.kind != ConstraintItemKind::kImplication &&
      item.kind != ConstraintItemKind::kIfElse &&
      item.kind != ConstraintItemKind::kForeach) {
    return RenderTerminatedItem(item);
  }
  const std::optional<std::string> kHead = RenderGoverningHead(item);
  const std::optional<std::string> kBody = RenderConstraintSet(item.body);
  if (!kHead || !kBody) return std::nullopt;
  if (!item.has_else) return VpiDecompileJoin({*kHead, *kBody});
  const std::optional<std::string> kElse = RenderConstraintSet(item.else_body);
  if (!kElse) return std::nullopt;
  return VpiDecompileJoin({*kHead, *kBody, "else", *kElse});
}

// §18.5: a constraint set or block, its items one space apart in braces.
std::optional<std::string> RenderConstraintSet(
    const std::vector<ConstraintItem*>& items) {
  std::vector<std::string> rendered;
  for (const ConstraintItem* item : items) {
    if (item == nullptr) return std::nullopt;
    std::optional<std::string> text = RenderConstraintItem(*item);
    if (!text) return std::nullopt;
    rendered.push_back(std::move(*text));
  }
  return "{" + VpiDecompileJoin(rendered) + "}";
}

// §18.7: a randomize() call's inline constraint block after `with`, the
// identifier list restricting it in the parentheses it is written in.
std::optional<std::string> RenderInlineConstraint(const Expr& expr) {
  const ClassMember* block = expr.inline_constraint;
  if (!block->constraint_items_parsed) return std::nullopt;
  const std::optional<std::string> kBlock =
      RenderConstraintSet(block->constraint_items);
  if (!kBlock) return std::nullopt;
  std::string ids;
  for (std::string_view id : expr.with_restrict_ids) {
    if (!ids.empty()) ids += ", ";
    ids += id;
  }
  return VpiDecompileJoin(
      {"with", expr.with_has_parens ? VpiDecompileParenthesize(ids) : "",
       *kBlock});
}

// §13.5 and §20: a call, its arguments in parentheses after the name; a system
// call written with none is its name alone.
std::optional<Piece> RenderCall(const Expr& expr) {
  std::string callee(expr.callee);
  if (expr.kind == ExprKind::kCall) {
    const std::optional<Piece> kCallee = Render(expr.lhs);
    if (!kCallee) return std::nullopt;
    callee = kCallee->text;
  } else if (expr.args.empty()) {
    return Piece{callee};
  }
  const std::optional<std::string> kArgs =
      RenderList(expr.args, expr.arg_names);
  if (!kArgs) return std::nullopt;
  std::string text = callee + "(" + *kArgs + ")";
  if (expr.inline_constraint != nullptr) {
    const std::optional<std::string> kWith = RenderInlineConstraint(expr);
    if (!kWith) return std::nullopt;
    return Piece{VpiDecompileJoin({text, *kWith})};
  }
  // §7.12: an array manipulation method's with clause, its expression in the
  // parentheses it is written in, or its array range in brackets (§7.12.1).
  if (expr.with_expr != nullptr) {
    const std::optional<Piece> kWith = Render(expr.with_expr);
    if (!kWith) return std::nullopt;
    text = VpiDecompileJoin({text, "with",
                             expr.with_has_parens
                                 ? VpiDecompileParenthesize(kWith->text)
                                 : kWith->text});
  }
  return Piece{text};
}

// §11.5.1 and §11.4.13: the separator between the two expressions of a part
// select, or of a range in an inside expression's set.
std::string_view RangeSeparator(const Expr& select) {
  if (select.is_part_select_plus) return "+:";
  if (select.is_part_select_minus) return "-:";
  if (select.op == TokenKind::kPlusSlashMinus) return "+/-";
  if (select.op == TokenKind::kPlusPercentMinus) return "+%-";
  return ":";
}

// §11.5.1: a bit select, part select or indexed part select after the
// expression it selects into; and §11.4.13: a range of an inside expression's
// set, which selects into nothing.
std::optional<Piece> RenderSelect(const Expr& expr) {
  std::string text;
  if (expr.base != nullptr) {
    const std::optional<Piece> kBase = Render(expr.base);
    if (!kBase) return std::nullopt;
    text = kBase->text;
  }
  const std::optional<Piece> kIndex = Render(expr.index);
  if (!kIndex) return std::nullopt;
  text += "[" + kIndex->text;
  if (expr.index_end != nullptr) {
    const std::optional<Piece> kEnd = Render(expr.index_end);
    if (!kEnd) return std::nullopt;
    text += std::string(RangeSeparator(expr)) + kEnd->text;
  }
  return Piece{text + "]"};
}

// §23.6 and §23.7: a member, or a name a scope resolves, after its prefix.
std::optional<Piece> RenderMemberAccess(const Expr& expr) {
  const std::optional<Piece> kBase = Render(expr.lhs);
  const std::optional<Piece> kMember = Render(expr.rhs);
  if (!kBase || !kMember) return std::nullopt;
  return Piece{kBase->text + (expr.is_scope_resolution ? "::" : ".") +
               kMember->text};
}

// §11.4.12: a concatenation, or a replication with its multiplier first.
std::optional<Piece> RenderConcatenation(const Expr& expr) {
  const std::optional<std::string> kElements = RenderList(expr.elements, {});
  if (!kElements) return std::nullopt;
  if (expr.kind == ExprKind::kConcatenation) {
    return Piece{"{" + *kElements + "}"};
  }
  const std::optional<Piece> kCount = Render(expr.repeat_count);
  if (!kCount) return std::nullopt;
  return Piece{"{" + kCount->text + "{" + *kElements + "}}"};
}

// §6.24.1: a cast, the type, size or signedness it casts to before the
// apostrophe and the expression cast in parentheses after it. A size written
// as more than a primary keeps the parentheses it needs.
std::optional<Piece> RenderCast(const Expr& expr) {
  std::string target(expr.text);
  if (target.empty()) {
    const std::optional<Piece> kTarget = Render(expr.rhs);
    if (!kTarget) return std::nullopt;
    const bool kWhole = kTarget->left == kUnsplit && kTarget->right == kUnsplit;
    target = kWhole ? kTarget->text : VpiDecompileParenthesize(kTarget->text);
  }
  const std::optional<Piece> kValue = Render(expr.lhs);
  if (!kValue) return std::nullopt;
  return Piece{target + "'" + VpiDecompileParenthesize(kValue->text)};
}

// §11.4.13: an inside expression, which binds its left operand as tightly as
// §11.3.2 has the relational operators bind theirs, and whose braced set
// nothing written after it can split.
std::optional<Piece> RenderInside(const Expr& expr) {
  const int kPower = InfixBindingPower(TokenKind::kLt).first;
  const std::optional<Piece> kValue = Render(expr.lhs);
  const std::optional<std::string> kSet = RenderList(expr.elements, {});
  if (!kValue || !kSet) return std::nullopt;
  const Piece kLeft = AsLeftOperand(*kValue, kPower);
  return Piece{VpiDecompileJoin({kLeft.text, "inside", "{" + *kSet + "}"}),
               std::min(kPower, kLeft.left), kUnsplit};
}

// §11.4.14: a streaming concatenation, its operator and any slice size one
// space apart before the braced expressions it streams.
std::optional<Piece> RenderStream(const Expr& expr) {
  std::string head = Spelling(expr.op);
  if (expr.lhs != nullptr) {
    const std::optional<Piece> kSlice = Render(expr.lhs);
    if (!kSlice) return std::nullopt;
    head = VpiDecompileJoin({head, kSlice->text});
  }
  const std::optional<std::string> kElements = RenderList(expr.elements, {});
  if (!kElements) return std::nullopt;
  return Piece{"{" + VpiDecompileJoin({head, "{" + *kElements + "}"}) + "}"};
}

// §11.11: a min:typ:max expression, its three expressions one space from the
// colons between them, in the parentheses a primary writes it in.
std::optional<Piece> RenderMinTypMax(const Expr& expr) {
  const std::optional<Piece> kMin = Render(expr.lhs);
  const std::optional<Piece> kTyp = Render(expr.condition);
  const std::optional<Piece> kMax = Render(expr.rhs);
  if (!kMin || !kTyp || !kMax) return std::nullopt;
  return Piece{VpiDecompileParenthesize(
      VpiDecompileJoin({kMin->text, ":", kTyp->text, ":", kMax->text}))};
}

// §23.6 and §3.12.1: a name, with the `$root.` or `pkg::` it was written
// under.
std::string IdentifierText(const Expr& expr) {
  std::string text;
  if (expr.scope_prefix == "$root") {
    text = "$root.";
  } else if (!expr.scope_prefix.empty()) {
    text = std::string(expr.scope_prefix) + "::";
  }
  return text + std::string(expr.text);
}

std::optional<Piece> Render(const Expr* expr) {
  if (expr == nullptr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return Piece{IdentifierText(*expr)};
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      if (expr->text.empty()) return std::nullopt;
      return Piece{std::string(expr->text)};
    case ExprKind::kUnary:
      return RenderUnary(*expr);
    case ExprKind::kBinary:
      return RenderBinary(*expr);
    case ExprKind::kTernary:
      return RenderConditional(*expr);
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      return RenderCall(*expr);
    case ExprKind::kSelect:
      return RenderSelect(*expr);
    case ExprKind::kMemberAccess:
      return RenderMemberAccess(*expr);
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return RenderConcatenation(*expr);
    case ExprKind::kCast:
      return RenderCast(*expr);
    case ExprKind::kInside:
      return RenderInside(*expr);
    case ExprKind::kStreamingConcat:
      return RenderStream(*expr);
    case ExprKind::kMinTypMax:
      return RenderMinTypMax(*expr);
    default:
      return std::nullopt;
  }
}

}  // namespace

std::string VpiExprDecompile(const Expr* expr) {
  const std::optional<Piece> kPiece = Render(expr);
  return kPiece ? kPiece->text : std::string();
}

}  // namespace delta
