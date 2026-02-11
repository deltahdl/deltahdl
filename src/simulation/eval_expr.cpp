#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
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
  uint32_t ew = (elem_width > 64) ? 64 : elem_width;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= inner_val << bit;
      if (bit + ew > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= inner_val >> (64 - bit);
      }
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

// §7.2: Extract a packed struct/union field from the base variable.
static Logic4Vec ExtractStructField(Variable* base_var,
                                    const StructTypeInfo* info,
                                    std::string_view field, Arena& arena) {
  for (const auto& f : info->fields) {
    if (f.name != field) continue;
    uint64_t val = base_var->value.ToUint64() >> f.bit_offset;
    uint64_t mask =
        (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
    return MakeLogic4VecVal(arena, f.width, val & mask);
  }
  return MakeLogic4Vec(arena, 1);
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string name;
  BuildMemberName(expr, name);
  auto* var = ctx.FindVariable(name);
  if (var) return var->value;

  // Try packed struct field extraction: split "base.field".
  auto dot = name.find('.');
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);
  auto* base_var = ctx.FindVariable(base_name);
  auto* sinfo = ctx.GetVariableStructType(base_name);
  if (base_var && sinfo)
    return ExtractStructField(base_var, sinfo, field_name, arena);
  // §7.12: Array property/method access (e.g., arr.sum, arr.sort).
  Logic4Vec arr_result;
  if (TryEvalArrayProperty(base_name, field_name, ctx, arena, arr_result))
    return arr_result;
  if (TryExecArrayPropertyStmt(base_name, field_name, ctx, arena))
    return MakeLogic4VecVal(arena, 1, 0);
  // §7.10: Queue property access (e.g., q.size).
  Logic4Vec queue_result;
  if (TryEvalQueueProperty(base_name, field_name, ctx, arena, queue_result))
    return queue_result;
  if (TryExecQueuePropertyStmt(base_name, field_name, ctx, arena))
    return MakeLogic4VecVal(arena, 1, 0);
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

// Parse a numeric string to uint32_t. Returns 0 if not a digit string.
static uint32_t ParseDigitStr(std::string_view text) {
  if (text.empty() || text[0] < '0' || text[0] > '9') return 0;
  uint32_t n = 0;
  for (char c : text) {
    if (c >= '0' && c <= '9') n = n * 10 + (c - '0');
  }
  return n;
}

// §11.4.14: Determine the slice size from the optional type/expression.
static uint32_t StreamSliceSize(const Expr* size_expr, SimContext& ctx,
                                Arena& arena) {
  if (!size_expr) return 1;
  if (size_expr->kind == ExprKind::kIdentifier) {
    uint32_t num = ParseDigitStr(size_expr->text);
    if (num > 0) return num;
    return CastWidth(size_expr->text);
  }
  auto val = EvalExpr(size_expr, ctx, arena).ToUint64();
  return (val == 0) ? 1 : static_cast<uint32_t>(val);
}

// Extract a slice of `slice_size` bits starting at `start_bit` from `src`.
static uint64_t ExtractSlice(const Logic4Vec& src, uint32_t start_bit,
                             uint32_t slice_size) {
  uint64_t result = 0;
  uint32_t bits_left = slice_size;
  uint32_t dst_bit = 0;
  while (bits_left > 0 && start_bit < src.width) {
    uint32_t word = start_bit / 64;
    uint32_t bit = start_bit % 64;
    uint32_t avail = 64 - bit;
    uint32_t take = (bits_left < avail) ? bits_left : avail;
    if (word < src.nwords) {
      uint64_t mask = (take >= 64) ? ~uint64_t{0} : (uint64_t{1} << take) - 1;
      result |= ((src.words[word].aval >> bit) & mask) << dst_bit;
    }
    dst_bit += take;
    start_bit += take;
    bits_left -= take;
  }
  return result;
}

// Place a `slice_size`-bit value at `start_bit` in `dst`.
static void PlaceSlice(Logic4Vec& dst, uint32_t start_bit, uint64_t val,
                       uint32_t slice_size) {
  uint32_t bits_left = slice_size;
  uint32_t src_bit = 0;
  while (bits_left > 0 && start_bit < dst.width) {
    uint32_t word = start_bit / 64;
    uint32_t bit = start_bit % 64;
    uint32_t avail = 64 - bit;
    uint32_t put = (bits_left < avail) ? bits_left : avail;
    if (word < dst.nwords) {
      uint64_t mask = (put >= 64) ? ~uint64_t{0} : (uint64_t{1} << put) - 1;
      dst.words[word].aval |= ((val >> src_bit) & mask) << bit;
    }
    src_bit += put;
    start_bit += put;
    bits_left -= put;
  }
}

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  // Concatenate all elements MSB-first (left-to-right = most significant).
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);

  auto concat = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    PlaceSlice(concat, bit_pos, it->ToUint64(), it->width);
    bit_pos += it->width;
  }

  // Right-shift streaming (>>) returns concatenation as-is.
  if (expr->op != TokenKind::kLtLt) return concat;

  // Left-shift streaming (<<): reverse order of slice_size-bit chunks.
  uint32_t ss = StreamSliceSize(expr->lhs, ctx, arena);
  uint32_t nslices = (total_width + ss - 1) / ss;
  auto result = MakeLogic4Vec(arena, total_width);
  for (uint32_t i = 0; i < nslices; ++i) {
    uint32_t src_start = i * ss;
    uint32_t dst_start = (nslices - 1 - i) * ss;
    uint64_t slice = ExtractSlice(concat, src_start, ss);
    PlaceSlice(result, dst_start, slice, ss);
  }
  return result;
}

// --- Assignment pattern (§10.9) ---

Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);

  // Evaluate all elements and compute total width.
  std::vector<Logic4Vec> parts;
  uint32_t total_width = 0;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 0);

  // Pack elements MSB-first (left-to-right = most significant first),
  // same as concatenation per IEEE 1800-2023 §10.9.1.
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    uint64_t val = it->ToUint64();
    uint32_t w = it->width;
    if (w > 64) w = 64;
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= val << bit;
      if (bit + w > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= val >> (64 - bit);
      }
    }
    bit_pos += it->width;
  }
  return result;
}

// --- Matches operator (§12.6) ---

Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);

  // §12.6: The matches operator compares the expression against a pattern.
  // For scalar/vector patterns, this is equality comparison.
  // X/Z bits in the pattern act as wildcards (don't-care).
  uint64_t la = lhs_val.ToUint64();
  uint64_t ra = rhs_val.ToUint64();
  uint64_t rb = (rhs_val.nwords > 0) ? rhs_val.words[0].bval : 0;

  // Mask out bits where the pattern has X or Z.
  uint64_t mask = ~rb;
  bool match = (la & mask) == (ra & mask);
  return MakeLogic4VecVal(arena, 1, match ? 1 : 0);
}

}  // namespace delta
