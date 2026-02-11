#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Method call extraction ---

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  return true;
}

// --- Replication ({n{expr}}) ---

Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, arena).ToUint64());
  if (count == 0 || expr->elements.empty()) return MakeLogic4Vec(arena, 1);

  // Evaluate inner elements as a concatenation.
  uint32_t elem_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    elem_width += parts.back().width;
  }
  // Concatenate inner elements into a single value.
  uint64_t inner_val = 0;
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    inner_val |= it->ToUint64() << bit_pos;
    bit_pos += it->width;
  }
  // Replicate the concatenated value.
  uint32_t total_width = elem_width * count;
  auto result = MakeLogic4Vec(arena, total_width);
  bit_pos = 0;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= inner_val << bit;
    }
    bit_pos += elem_width;
  }
  return result;
}

// --- Prefix increment/decrement (§11.4.2) ---

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  uint64_t v = old_val.ToUint64();
  uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
  auto new_val = MakeLogic4VecVal(arena, old_val.width, nv);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = new_val;
  }
  return new_val;  // Return new value (prefix semantics).
}

// --- Postfix increment/decrement (§11.4.2) ---

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  uint64_t v = old_val.ToUint64();
  uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = MakeLogic4VecVal(arena, old_val.width, nv);
  }
  return old_val;  // Return original value (postfix semantics).
}

// --- Member access (a.b) ---

static void BuildMemberName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildMemberName(expr->lhs, out);
    out += ".";
    BuildMemberName(expr->rhs, out);
  }
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string name;
  BuildMemberName(expr, name);
  auto* var = ctx.FindVariable(name);
  if (var) return var->value;
  return MakeLogic4Vec(arena, 1);
}

// --- Cast (type'(expr)) (§6.24) ---

static uint32_t CastWidth(std::string_view type_name) {
  if (type_name == "byte") return 8;
  if (type_name == "shortint") return 16;
  if (type_name == "int") return 32;
  if (type_name == "longint") return 64;
  if (type_name == "integer") return 32;
  if (type_name == "bit") return 1;
  if (type_name == "logic") return 1;
  if (type_name == "reg") return 1;
  return 32;  // Default to 32-bit.
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto inner = EvalExpr(expr->lhs, ctx, arena);
  uint32_t target_width = CastWidth(expr->text);
  uint64_t val = inner.ToUint64();
  // Truncate or zero-extend to target width.
  if (target_width < 64) {
    val &= (uint64_t{1} << target_width) - 1;
  }
  return MakeLogic4VecVal(arena, target_width, val);
}

// --- Inside operator (§11.4.13) ---

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint64_t lv = EvalExpr(expr->lhs, ctx, arena).ToUint64();
  for (auto* elem : expr->elements) {
    if (elem->kind == ExprKind::kSelect && elem->index && elem->index_end) {
      // Range element [lo:hi].
      uint64_t lo = EvalExpr(elem->index, ctx, arena).ToUint64();
      uint64_t hi = EvalExpr(elem->index_end, ctx, arena).ToUint64();
      if (lo > hi) std::swap(lo, hi);
      if (lv >= lo && lv <= hi) return MakeLogic4VecVal(arena, 1, 1);
    } else {
      uint64_t ev = EvalExpr(elem, ctx, arena).ToUint64();
      if (lv == ev) return MakeLogic4VecVal(arena, 1, 1);
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// --- Streaming concatenation (§11.4.14) ---

static uint64_t ReverseBits(uint64_t val, uint32_t width) {
  uint64_t result = 0;
  for (uint32_t i = 0; i < width; ++i) {
    result |= ((val >> i) & 1) << (width - 1 - i);
  }
  return result;
}

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  // Concatenate all elements.
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);

  uint64_t concat_val = 0;
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    concat_val |= it->ToUint64() << bit_pos;
    bit_pos += it->width;
  }
  // Left-shift streaming (<<) reverses bit order.
  if (expr->op == TokenKind::kLtLt) {
    concat_val = ReverseBits(concat_val, total_width);
  }
  return MakeLogic4VecVal(arena, total_width, concat_val);
}

}  // namespace delta
