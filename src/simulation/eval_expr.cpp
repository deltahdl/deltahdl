#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
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
  // Concatenate inner elements into a single aval/bval pair.
  uint64_t inner_aval = 0;
  uint64_t inner_bval = 0;
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    inner_aval |= it->ToUint64() << bit_pos;
    uint64_t bv = (it->nwords > 0) ? it->words[0].bval : 0;
    inner_bval |= bv << bit_pos;
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
      result.words[word].aval |= inner_aval << bit;
      result.words[word].bval |= inner_bval << bit;
      if (bit + ew > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= inner_aval >> (64 - bit);
        result.words[word + 1].bval |= inner_bval >> (64 - bit);
      }
    }
    bit_pos += elem_width;
  }
  return result;
}

// --- Prefix increment/decrement (§11.4.2) ---

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    // §11.4.2: Real increment/decrement by 1.0.
    double d = 0.0;
    uint64_t bits = old_val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    d += (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0;
    std::memcpy(&bits, &d, sizeof(double));
    new_val = MakeLogic4VecVal(arena, 64, bits);
    new_val.is_real = true;
  } else {
    uint64_t v = old_val.ToUint64();
    uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
    new_val = MakeLogic4VecVal(arena, old_val.width, nv);
  }
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = new_val;
  }
  return new_val;  // Return new value (prefix semantics).
}

// --- Postfix increment/decrement (§11.4.2) ---

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) {
      if (old_val.is_real) {
        double d = 0.0;
        uint64_t bits = old_val.ToUint64();
        std::memcpy(&d, &bits, sizeof(double));
        d += (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0;
        std::memcpy(&bits, &d, sizeof(double));
        var->value = MakeLogic4VecVal(arena, 64, bits);
        var->value.is_real = true;
      } else {
        uint64_t v = old_val.ToUint64();
        uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
        var->value = MakeLogic4VecVal(arena, old_val.width, nv);
      }
    }
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

// §7.12/§7.10/§7.8: Try collection property/method access.
static bool TryCollectionAccess(std::string_view base, std::string_view field,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalArrayProperty(base, field, ctx, arena, out)) return true;
  if (TryExecArrayPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalQueueProperty(base, field, ctx, arena, out)) return true;
  if (TryExecQueuePropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalAssocProperty(base, field, ctx, arena, out)) return true;
  if (TryExecAssocPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
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
  if (base_var && sinfo) {
    // §11.9: Tagged union — tag mismatch returns X.
    if (sinfo->is_union) {
      auto tag = ctx.GetVariableTag(base_name);
      if (!tag.empty() && tag != field_name)
        return MakeAllX(arena, sinfo->total_width);
    }
    return ExtractStructField(base_var, sinfo, field_name, arena);
  }
  // §8: Class object property access (e.g., obj.a).
  if (base_var) {
    auto handle = base_var->value.ToUint64();
    auto* obj = ctx.GetClassObject(handle);
    if (obj) return obj->GetProperty(field_name, arena);
  }
  Logic4Vec coll_result;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, coll_result))
    return coll_result;
  return MakeLogic4Vec(arena, 1);
}

// --- Cast (type'(expr)) (§6.24) ---

static uint32_t CastWidth(std::string_view type_name) {
  if (type_name == "byte") return 8;
  if (type_name == "shortint") return 16;
  if (type_name == "int") return 32;
  if (type_name == "longint") return 64;
  if (type_name == "integer") return 32;
  if (type_name == "real" || type_name == "realtime") return 64;
  if (type_name == "shortreal") return 32;
  if (type_name == "bit") return 1;
  if (type_name == "logic") return 1;
  if (type_name == "reg") return 1;
  if (type_name == "string") return 0;  // String cast handled separately.
  return 32;                            // Default to 32-bit.
}

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  double d = 0.0;
  uint64_t bits = vec.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// §6.24.3: Pack unpacked array elements into a bitvector (index 0 at MSBs).
static Logic4Vec PackArrayBitStream(std::string_view name,
                                    const ArrayInfo& info, SimContext& ctx,
                                    Arena& arena) {
  uint32_t total_bits = info.size * info.elem_width;
  uint64_t packed = 0;
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(elem_name);
    if (!elem) continue;
    uint64_t ev = elem->value.ToUint64();
    uint32_t shift = total_bits - (i + 1) * info.elem_width;
    packed |= (ev & ((uint64_t{1} << info.elem_width) - 1)) << shift;
  }
  return MakeLogic4VecVal(arena, total_bits, packed);
}

// §6.12.1: Handle real↔integer conversion in cast.
static Logic4Vec CastRealConversion(const Logic4Vec& inner,
                                    std::string_view type_name,
                                    uint32_t target_width, Arena& arena) {
  if (inner.is_real && !IsRealCastTarget(type_name)) {
    auto val = static_cast<uint64_t>(
        static_cast<int64_t>(std::llround(ExtractDouble(inner))));
    if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
    return MakeLogic4VecVal(arena, target_width, val);
  }
  auto d = static_cast<double>(inner.ToUint64());
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, target_width, bits);
  result.is_real = true;
  return result;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  // §6.24.3: Detect bit-stream source (unpacked array).
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier) {
    auto* arr_info = ctx.FindArrayInfo(expr->lhs->text);
    if (arr_info && arr_info->size > 0) {
      auto inner = PackArrayBitStream(expr->lhs->text, *arr_info, ctx, arena);
      uint32_t target_width = CastWidth(expr->text);
      uint64_t val = inner.ToUint64();
      if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
      return MakeLogic4VecVal(arena, target_width, val);
    }
  }
  auto inner = EvalExpr(expr->lhs, ctx, arena);
  std::string_view type_name = expr->text;
  // §6.24.1: signed'(x) / unsigned'(x) change signedness, not width.
  if (type_name == "signed") {
    inner.is_signed = true;
    return inner;
  }
  if (type_name == "unsigned" || type_name == "const") {
    inner.is_signed = false;
    return inner;
  }
  uint32_t target_width = CastWidth(type_name);
  // §6.12.1: real↔integer conversion.
  if (inner.is_real != IsRealCastTarget(type_name)) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  uint64_t val = inner.ToUint64();
  if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
  return MakeLogic4VecVal(arena, target_width, val);
}

// --- Inside operator (§11.4.13) ---

// Resolve a $ bound to type min (lower=true) or type max (lower=false).
static uint64_t ResolveDollarBound(uint32_t width, bool lower) {
  if (lower) return 0;
  if (width >= 64) return ~uint64_t{0};
  return (uint64_t{1} << width) - 1;
}

// Compute tolerance range bounds: [A +/- B] or [A +%- B].
static void ComputeToleranceBounds(uint64_t a, uint64_t b, TokenKind op,
                                   uint64_t& lo, uint64_t& hi) {
  uint64_t tol = b;
  if (op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
  lo = (a >= tol) ? a - tol : 0;
  hi = a + tol;
  if (lo > hi) std::swap(lo, hi);
}

// Returns: 1=match, 0=no-match, 2=ambiguous.
static int InsideMatchTolerance(uint64_t lv, const Expr* elem, SimContext& ctx,
                                Arena& arena) {
  auto a_v = EvalExpr(elem->index, ctx, arena);
  auto b_v = EvalExpr(elem->index_end, ctx, arena);
  if (!a_v.IsKnown() || !b_v.IsKnown()) return 2;
  uint64_t lo = 0;
  uint64_t hi = 0;
  ComputeToleranceBounds(a_v.ToUint64(), b_v.ToUint64(), elem->op, lo, hi);
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

static bool IsDollarExpr(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

static int InsideMatchRange(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  if (!lhs.IsKnown()) return 2;
  uint64_t lv = lhs.ToUint64();
  // §11.4.13: Tolerance range [A +/- B] or [A +%- B].
  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus) {
    return InsideMatchTolerance(lv, elem, ctx, arena);
  }
  // §11.4.13: Normal range with possible $ bounds.
  uint64_t lo = IsDollarExpr(elem->index)
                    ? ResolveDollarBound(lhs.width, true)
                    : EvalExpr(elem->index, ctx, arena).ToUint64();
  uint64_t hi = IsDollarExpr(elem->index_end)
                    ? ResolveDollarBound(lhs.width, false)
                    : EvalExpr(elem->index_end, ctx, arena).ToUint64();
  if (lo > hi) std::swap(lo, hi);
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

static int InsideMatchValue(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  auto ev = EvalExpr(elem, ctx, arena);
  if (!lhs.IsKnown() || !ev.IsKnown()) return 2;
  return (lhs.ToUint64() == ev.ToUint64()) ? 1 : 0;
}

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    bool is_range =
        elem->kind == ExprKind::kSelect && elem->index && elem->index_end;
    int r = is_range ? InsideMatchRange(lhs, elem, ctx, arena)
                     : InsideMatchValue(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    x.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    return x;
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

// §11.4.14.1: Expand an unpacked array identifier into its element values.
static void ExpandArrayElements(std::string_view name, SimContext& ctx,
                                std::vector<Logic4Vec>& parts,
                                uint32_t& total_width) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  for (uint32_t i = 0; i < info->size; ++i) {
    std::string elem_name =
        std::string(name) + "[" + std::to_string(info->lo + i) + "]";
    auto* var = ctx.FindVariable(elem_name);
    if (var) {
      parts.push_back(var->value);
    } else {
      parts.push_back(MakeLogic4Vec(ctx.GetArena(), info->elem_width));
    }
    total_width += parts.back().width;
  }
}

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  // Concatenate all elements MSB-first (left-to-right = most significant).
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    // §11.4.14.1: If element is an unpacked array, expand its elements.
    if (elem->kind == ExprKind::kIdentifier && ctx.FindArrayInfo(elem->text)) {
      ExpandArrayElements(elem->text, ctx, parts, total_width);
    } else {
      parts.push_back(EvalExpr(elem, ctx, arena));
      total_width += parts.back().width;
    }
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
  return AssembleConcatParts(parts, total_width, arena);
}

// --- Structure assignment pattern (§10.9.2) ---

static void PlaceFieldValue(Logic4Vec& result, const StructFieldInfo& f,
                            uint64_t val) {
  uint64_t mask = (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
  uint64_t bits = (val & mask) << f.bit_offset;
  result.words[0].aval |= bits;
}

static DataTypeKind TypeKeyToKind(std::string_view key) {
  if (key == "int") return DataTypeKind::kInt;
  if (key == "integer") return DataTypeKind::kInteger;
  if (key == "logic") return DataTypeKind::kLogic;
  if (key == "reg") return DataTypeKind::kReg;
  if (key == "byte") return DataTypeKind::kByte;
  if (key == "shortint") return DataTypeKind::kShortint;
  if (key == "longint") return DataTypeKind::kLongint;
  if (key == "bit") return DataTypeKind::kBit;
  if (key == "real") return DataTypeKind::kReal;
  if (key == "shortreal") return DataTypeKind::kShortreal;
  if (key == "string") return DataTypeKind::kString;
  return DataTypeKind::kImplicit;
}

static bool IsMemberNameKey(std::string_view key, const StructTypeInfo* info) {
  for (const auto& f : info->fields) {
    if (f.name == key) return true;
  }
  return false;
}

struct PatternState {
  Logic4Vec& result;
  std::vector<bool>& assigned;
  SimContext& ctx;
  Arena& arena;
};

// Pass 1: Assign fields by explicit member name (highest precedence).
static void ApplyMemberKeys(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size()) break;
    if (!IsMemberNameKey(expr->pattern_keys[i], info)) continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (info->fields[fi].name != expr->pattern_keys[i]) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
      s.assigned[fi] = true;
      break;
    }
  }
}

// Pass 2: Assign unset fields by type key (middle precedence).
static void ApplyTypeKeys(const Expr* expr, const StructTypeInfo* info,
                          PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size()) break;
    auto kind = TypeKeyToKind(expr->pattern_keys[i]);
    if (kind == DataTypeKind::kImplicit) continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi] || info->fields[fi].type_kind != kind) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
      s.assigned[fi] = true;
    }
  }
}

// Pass 3: Assign all remaining unset fields from 'default' key.
static void ApplyDefaultKey(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size() || expr->pattern_keys[i] != "default")
      continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi]) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
    }
    return;
  }
}

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena) {
  auto result = MakeLogic4Vec(arena, info->total_width);
  std::vector<bool> assigned(info->fields.size(), false);
  PatternState state{result, assigned, ctx, arena};
  ApplyMemberKeys(expr, info, state);
  ApplyTypeKeys(expr, info, state);
  ApplyDefaultKey(expr, info, state);
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

// --- Select (bit/part) ---

// §7.10: Resolve a queue index with $ = last element index.
static uint64_t ResolveQueueIdx(const Expr* idx_expr, QueueObject* q,
                                SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  uint64_t last = q->elements.empty() ? 0 : q->elements.size() - 1;
  dv->value = MakeLogic4VecVal(arena, 32, last);
  auto val = EvalExpr(idx_expr, ctx, arena);
  ctx.PopScope();
  return val.ToUint64();
}

static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena);
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : MakeAllX(arena, q->elem_width);
  return true;
}

static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Arena& arena,
                                  Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto elem_name =
      std::string(expr->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  if (!elem) {
    out = MakeAllX(arena, info->elem_width);
    return true;
  }
  out = elem->value;
  return true;
}

static bool BuildCompoundName(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundName(expr->base, ctx, arena, name)) return false;
  auto idx = EvalExpr(expr->index, ctx, arena).ToUint64();
  name += "[" + std::to_string(idx) + "]";
  return true;
}

static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  if (!BuildCompoundName(expr, ctx, arena, compound)) return false;
  auto* elem = ctx.FindVariable(compound);
  if (!elem) return false;
  out = elem->value;
  return true;
}

static bool TryArraySliceSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (!expr->index_end || !expr->base) return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto hi_val = EvalExpr(expr->index, ctx, arena).ToUint64();
  auto lo_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  auto lo = std::min(hi_val, lo_val);
  auto hi = std::max(hi_val, lo_val);
  auto count = static_cast<uint32_t>(hi - lo + 1);
  uint32_t ew = info->elem_width;
  out = MakeLogic4Vec(arena, count * ew);
  for (uint32_t i = 0; i < count; ++i) {
    auto n = std::string(expr->base->text) + "[" + std::to_string(lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    auto val = v ? v->value.ToUint64() : 0;
    uint32_t bit_off = i * ew;
    out.words[bit_off / 64].aval |= (val & ((1ULL << ew) - 1))
                                    << (bit_off % 64);
  }
  return true;
}

static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, uint64_t idx,
                                uint64_t end_idx, Arena& arena) {
  auto lo = static_cast<uint32_t>(std::min(idx, end_idx));
  auto hi = static_cast<uint32_t>(std::max(idx, end_idx));
  uint32_t width = hi - lo + 1;
  uint64_t val = base_val.ToUint64() >> lo;
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  auto result = MakeLogic4VecVal(arena, width, val & mask);
  // §11.5.1: OOB bits → X. Mark bits beyond base_val.width as X.
  if (hi >= base_val.width && result.nwords > 0) {
    uint32_t first_oob = (base_val.width > lo) ? base_val.width - lo : 0;
    for (uint32_t b = first_oob; b < width && b < 64; ++b) {
      result.words[0].aval |= uint64_t{1} << b;
      result.words[0].bval |= uint64_t{1} << b;
    }
  }
  return result;
}

static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  return aa->has_default ? aa->default_value
                         : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

static std::string ExtractStringKey(const Logic4Vec& key) {
  uint32_t nb = key.width / 8;
  std::string s;
  s.reserve(nb);
  for (uint32_t i = nb; i > 0; --i) {
    uint32_t bi = i - 1;
    auto ch = static_cast<char>(
        (key.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
    if (ch != 0) s.push_back(ch);
  }
  return s;
}

static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx) {
  if (!aa->has_default)
    ctx.GetDiag().Warning({}, "associative array '" + std::string(name) +
                                  "': read of non-existent index");
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = ExtractStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto key = static_cast<int64_t>(EvalExpr(idx_expr, ctx, arena).ToUint64());
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* aa = ctx.FindAssocArray(expr->base->text);
  if (!aa) return false;
  out = aa->is_string_key
            ? AssocReadStr(aa, expr->index, expr->base->text, ctx, arena)
            : AssocReadInt(aa, expr->index, expr->base->text, ctx, arena);
  return true;
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      uint64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  if (expr->is_part_select_plus) {
    auto w = static_cast<uint32_t>(end_val);
    return EvalPartSelect(base, idx, idx + w - 1, arena);
  }
  if (expr->is_part_select_minus) {
    auto w = static_cast<uint32_t>(end_val);
    uint64_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
    return EvalPartSelect(base, lo, idx, arena);
  }
  return EvalPartSelect(base, idx, end_val, arena);
}

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  // §11.5.1: X/Z index → return X for packed bit/part-select.
  if (HasUnknownBits(idx_val)) {
    if (expr->index_end) {
      auto w = static_cast<uint32_t>(
          EvalExpr(expr->index_end, ctx, arena).ToUint64());
      return MakeAllX(arena, w > 0 ? w : 1);
    }
    return MakeAllX(arena, 1);
  }
  uint64_t idx = idx_val.ToUint64();
  if (TryArrayElementSelect(expr, idx, ctx, arena, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;
  if (TryArraySliceSelect(expr, ctx, arena, result)) return result;
  auto base_val = EvalExpr(expr->base, ctx, arena);
  if (expr->index_end)
    return EvalPackedPartSelect(expr, base_val, idx, ctx, arena);
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> idx) & 1);
}

}  // namespace delta
