#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static uint32_t ParseDigitIdentifier(std::string_view text) {
  uint32_t n = 0;
  for (char c : text) {
    if (c >= '0' && c <= '9') n = n * 10 + (c - '0');
  }
  return n > 0 ? n : 1;
}

static uint32_t TypeNameToSliceWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "int" || t == "integer") return 32;
  if (t == "longint") return 64;
  if (t == "real" || t == "realtime") return 64;
  if (t == "shortreal") return 32;
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  return 32;
}

static uint32_t StreamSliceSizeForUnpack(const Expr* size_expr, SimContext& ctx,
                                         Arena& arena) {
  if (!size_expr) return 1;
  if (size_expr->kind == ExprKind::kIdentifier) {
    if (!size_expr->text.empty() && size_expr->text[0] >= '0' &&
        size_expr->text[0] <= '9') {
      return ParseDigitIdentifier(size_expr->text);
    }
    return TypeNameToSliceWidth(size_expr->text);
  }
  auto val = EvalExpr(size_expr, ctx, arena).ToUint64();
  auto sval = static_cast<int64_t>(val);
  if (val == 0 || sval < 0) {
    ctx.GetDiag().Error({},
                        "slice_size for streaming operator must be positive");
    return 1;
  }
  return static_cast<uint32_t>(val);
}

struct StreamElemInfo {
  const Expr* expr;
  uint32_t width;
  std::string target_name;
};

// Single-index with-range (no index_end): one element at `idx`, or
// out-of-range.
static bool ResolveSingleIndexRange(int64_t idx, uint32_t array_size,
                                    uint32_t array_lo, uint32_t& out_start,
                                    uint32_t& out_count) {
  int64_t rel = idx - static_cast<int64_t>(array_lo);
  if (rel < 0 || static_cast<uint32_t>(rel) >= array_size) {
    out_start = 0;
    out_count = 0;
    return false;
  }
  out_start = static_cast<uint32_t>(rel);
  out_count = 1;
  return true;
}

// [idx +: idx2] indexed part-select.
static void ResolvePlusPartSelectRange(int64_t idx, int64_t idx2,
                                       uint32_t array_lo, uint32_t& out_start,
                                       uint32_t& out_count) {
  int64_t rel = idx - static_cast<int64_t>(array_lo);
  out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
  out_count = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
}

// [idx -: idx2] indexed part-select.
static void ResolveMinusPartSelectRange(int64_t idx, int64_t idx2,
                                        uint32_t array_lo, uint32_t& out_start,
                                        uint32_t& out_count) {
  uint32_t width = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
  int64_t lo_idx = idx - static_cast<int64_t>(width) + 1;
  int64_t rel = lo_idx - static_cast<int64_t>(array_lo);
  out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
  out_count = width;
}

// [idx : idx2] explicit range (either direction).
static void ResolveExplicitRange(int64_t idx, int64_t idx2, uint32_t array_lo,
                                 uint32_t& out_start, uint32_t& out_count) {
  int64_t lo = idx, hi = idx2;
  if (lo > hi) std::swap(lo, hi);
  int64_t rel_lo = lo - static_cast<int64_t>(array_lo);
  out_start = (rel_lo < 0) ? 0 : static_cast<uint32_t>(rel_lo);
  out_count = static_cast<uint32_t>(hi - lo + 1);
}

bool ResolveWithRange(const Expr* with_expr, SimContext& ctx, Arena& arena,
                      uint32_t array_size, uint32_t array_lo,
                      uint32_t& out_start, uint32_t& out_count) {
  if (!with_expr || with_expr->kind != ExprKind::kSelect) {
    out_start = 0;
    out_count = array_size;
    return true;
  }
  int64_t idx =
      static_cast<int64_t>(EvalExpr(with_expr->index, ctx, arena).ToUint64());
  if (!with_expr->index_end) {
    return ResolveSingleIndexRange(idx, array_size, array_lo, out_start,
                                   out_count);
  }
  int64_t idx2 = static_cast<int64_t>(
      EvalExpr(with_expr->index_end, ctx, arena).ToUint64());
  if (with_expr->is_part_select_plus) {
    ResolvePlusPartSelectRange(idx, idx2, array_lo, out_start, out_count);
  } else if (with_expr->is_part_select_minus) {
    ResolveMinusPartSelectRange(idx, idx2, array_lo, out_start, out_count);
  } else {
    ResolveExplicitRange(idx, idx2, array_lo, out_start, out_count);
  }
  return true;
}

// Whether any bare (non-with) identifier element is a dynamic queue, which
// makes the unpack greedily size that queue from the leftover stream bits.
static bool LhsHasGreedyDynamicElement(const Expr* lhs, SimContext& ctx) {
  for (auto* elem : lhs->elements) {
    if (elem->with_expr) continue;
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text)) {
      return true;
    }
  }
  return false;
}

// Bit width contributed by a with-range identifier element (fixed array or
// queue) when computing the fixed-target sum.
static uint32_t FixedWithRangeElementWidth(const Expr* elem, SimContext& ctx,
                                           Arena& arena) {
  if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
    uint32_t start = 0, count = 0;
    ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size, ainfo->lo, start,
                     count);
    if (start + count > ainfo->size)
      count = (start < ainfo->size) ? ainfo->size - start : 0;
    return count * ainfo->elem_width;
  }
  if (auto* queue = ctx.FindQueue(elem->text)) {
    uint32_t start = 0, count = 0;
    ResolveWithRange(elem->with_expr, ctx, arena,
                     static_cast<uint32_t>(queue->elements.size()), 0, start,
                     count);
    return count * queue->elem_width;
  }
  return 0;
}

// Sum of bit widths of all non-greedy (fixed) targets, used to compute how
// many bits remain for the single greedy dynamic queue.
static uint32_t SumFixedElementWidths(const Expr* lhs, SimContext& ctx,
                                      Arena& arena) {
  uint32_t fixed_sum = 0;
  for (auto* elem : lhs->elements) {
    if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
      fixed_sum += FixedWithRangeElementWidth(elem, ctx, arena);
      continue;
    }
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text))
      continue;
    auto* var = ResolveLhsVariable(elem, ctx);
    if (var) fixed_sum += var->value.width;
  }
  return fixed_sum;
}

// Collect targets for a fixed-array with-range element. Returns bits added.
static uint32_t CollectArrayWithRangeElements(
    const Expr* elem, ArrayInfo* ainfo, SimContext& ctx, Arena& arena,
    std::vector<StreamElemInfo>& elems) {
  uint32_t start = 0, count = 0;
  bool in_range = ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size,
                                   ainfo->lo, start, count);
  if (!in_range || start + count > ainfo->size) {
    uint32_t clamped = (start < ainfo->size) ? ainfo->size - start : 0;
    ctx.GetDiag().Error(
        {}, "streaming unpack with-range exceeds fixed array bounds");
    count = clamped;
  }
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t abs_idx = ainfo->lo + start + i;
    std::string name =
        std::string(elem->text) + "[" + std::to_string(abs_idx) + "]";
    elems.push_back({elem, ainfo->elem_width, std::move(name)});
    added += ainfo->elem_width;
  }
  return added;
}

// Collect targets for a queue with-range element, growing the queue as needed.
// Returns bits added.
static uint32_t CollectQueueWithRangeElements(
    const Expr* elem, QueueObject* queue, SimContext& ctx, Arena& arena,
    std::vector<StreamElemInfo>& elems) {
  uint32_t start = 0, count = 0;
  ResolveWithRange(elem->with_expr, ctx, arena,
                   static_cast<uint32_t>(queue->elements.size()), 0, start,
                   count);
  uint32_t needed = start + count;
  while (queue->elements.size() < needed) {
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  }
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    std::string name =
        std::string(elem->text) + "__q__" + std::to_string(start + i);
    elems.push_back({elem, queue->elem_width, std::move(name)});
    added += queue->elem_width;
  }
  return added;
}

// Collect targets for the (single) greedy dynamic queue, sized from the bits
// left after all fixed targets. Returns bits added.
static uint32_t CollectGreedyQueueElements(const Expr* elem, QueueObject* queue,
                                           uint32_t rhs_width,
                                           uint32_t fixed_sum, Arena& arena,
                                           std::vector<StreamElemInfo>& elems) {
  uint32_t remaining = (rhs_width > fixed_sum) ? rhs_width - fixed_sum : 0;
  uint32_t count = queue->elem_width > 0 ? remaining / queue->elem_width : 0;
  queue->elements.clear();
  for (uint32_t i = 0; i < count; ++i) {
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  }
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    std::string name = std::string(elem->text) + "__q__" + std::to_string(i);
    elems.push_back({elem, queue->elem_width, std::move(name)});
    added += queue->elem_width;
  }
  return added;
}

// Try to collect a with-range element (fixed array or queue). Returns true and
// sets `added` if the element was a with-range identifier handled here.
static bool TryCollectWithRangeElement(const Expr* elem, SimContext& ctx,
                                       Arena& arena,
                                       std::vector<StreamElemInfo>& elems,
                                       uint32_t& added) {
  if (!elem->with_expr || elem->kind != ExprKind::kIdentifier) return false;
  if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
    added = CollectArrayWithRangeElements(elem, ainfo, ctx, arena, elems);
    return true;
  }
  if (auto* queue = ctx.FindQueue(elem->text)) {
    added = CollectQueueWithRangeElements(elem, queue, ctx, arena, elems);
    return true;
  }
  return false;
}

// Try to collect a bare dynamic-queue element under greedy sizing. Returns true
// if the element was such a queue (the first one is sized greedily; subsequent
// ones are cleared). Sets `added` for the greedy queue.
static bool TryCollectGreedyDynamicElement(const Expr* elem, SimContext& ctx,
                                           Arena& arena, uint32_t rhs_width,
                                           uint32_t fixed_sum,
                                           bool& first_dynamic_consumed,
                                           std::vector<StreamElemInfo>& elems,
                                           uint32_t& added) {
  if (elem->with_expr || elem->kind != ExprKind::kIdentifier) return false;
  auto* queue = ctx.FindQueue(elem->text);
  if (!queue) return false;
  if (!first_dynamic_consumed) {
    first_dynamic_consumed = true;
    added = CollectGreedyQueueElements(elem, queue, rhs_width, fixed_sum, arena,
                                       elems);
  } else {
    queue->elements.clear();
  }
  return true;
}

static uint32_t CollectStreamElements(const Expr* lhs, SimContext& ctx,
                                      Arena& arena,
                                      std::vector<StreamElemInfo>& elems,
                                      uint32_t rhs_width) {
  bool has_dynamic = LhsHasGreedyDynamicElement(lhs, ctx);

  uint32_t fixed_sum = has_dynamic ? SumFixedElementWidths(lhs, ctx, arena) : 0;

  uint32_t total_width = 0;
  bool first_dynamic_consumed = false;
  for (auto* elem : lhs->elements) {
    uint32_t added = 0;
    if (TryCollectWithRangeElement(elem, ctx, arena, elems, added)) {
      total_width += added;
      continue;
    }
    if (has_dynamic &&
        TryCollectGreedyDynamicElement(elem, ctx, arena, rhs_width, fixed_sum,
                                       first_dynamic_consumed, elems, added)) {
      total_width += added;
      continue;
    }
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    elems.push_back({elem, var->value.width, {}});
    total_width += var->value.width;
  }
  return total_width;
}

// Copy a single bit position `sbit` of `src` into bit position `dbit` of `dst`.
// Out-of-range source words contribute nothing.
static void CopyOneStreamBit(const Logic4Vec& src, Logic4Vec& dst,
                             uint32_t sbit, uint32_t dbit) {
  uint32_t sw = sbit / 64, sb = sbit % 64;
  uint32_t dw = dbit / 64, db = dbit % 64;
  if (sw >= src.nwords) return;
  if ((src.words[sw].aval >> sb) & 1) dst.words[dw].aval |= uint64_t{1} << db;
  if ((src.words[sw].bval >> sb) & 1) dst.words[dw].bval |= uint64_t{1} << db;
}

// Copy `bits_to_copy` bits from `stream`[src_start..] into `dst`[dst_start..],
// stopping at total_width.
static void CopyStreamSliceBits(const Logic4Vec& stream, Logic4Vec& dst,
                                uint32_t src_start, uint32_t dst_start,
                                uint32_t bits_to_copy, uint32_t total_width) {
  for (uint32_t b = 0; b < bits_to_copy; ++b) {
    uint32_t dbit = dst_start + b;
    if (dbit >= total_width) break;
    CopyOneStreamBit(stream, dst, src_start + b, dbit);
  }
}

static Logic4Vec ReverseStreamSlices(const Logic4Vec& stream,
                                     uint32_t total_width, uint32_t ss,
                                     Arena& arena) {
  uint32_t nslices = (total_width + ss - 1) / ss;
  auto reordered = MakeLogic4Vec(arena, total_width);
  for (uint32_t i = 0; i < nslices; ++i) {
    uint32_t src_start = i * ss;
    uint32_t dst_start =
        total_width > (i + 1) * ss ? total_width - (i + 1) * ss : 0;
    uint32_t bits_to_copy = ss;
    if (src_start + bits_to_copy > total_width)
      bits_to_copy = total_width - src_start;
    CopyStreamSliceBits(stream, reordered, src_start, dst_start, bits_to_copy,
                        total_width);
  }
  return reordered;
}

static Logic4Vec ExtractStreamBits(const Logic4Vec& stream, uint32_t bit_offset,
                                   uint32_t width, uint32_t total_width,
                                   Arena& arena) {
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t sbit = bit_offset + b;
    if (sbit >= total_width) break;
    CopyOneStreamBit(stream, result, sbit, b);
  }
  return result;
}

// Whether `e` (or any operand it is built from) names one of `names`.
static bool ExprRefsIdentifierIn(const Expr* e,
                                 const std::vector<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) {
    for (auto n : names)
      if (n == e->text) return true;
  }
  return ExprRefsIdentifierIn(e->index, names) ||
         ExprRefsIdentifierIn(e->index_end, names) ||
         ExprRefsIdentifierIn(e->lhs, names) ||
         ExprRefsIdentifierIn(e->rhs, names) ||
         ExprRefsIdentifierIn(e->base, names);
}

// §11.4.14.4: a with-range expression is evaluated immediately before its array
// is unpacked, so when it refers to a field that this same operator unpacks to
// its left, the just-unpacked value must drive the range. The default unpack
// pass resolves every with-range up front (before any write-back), which only
// satisfies the complementary case — a reference to a field unpacked to the
// right uses that field's previous value. This predicate detects the
// left-reference case (a with-range naming an earlier scalar target) so it can
// be routed to a forward, write-as-you-go unpack instead. It is limited to the
// right-shift form with no greedy dynamic operand, where stream bits map
// MSB-first onto elements in order and the forward pass is exact.
static bool ShouldForwardResolveUnpack(const Expr* lhs, SimContext& ctx) {
  if (lhs->op == TokenKind::kLtLt) return false;
  std::vector<std::string_view> earlier;
  bool dependency = false;
  for (auto* elem : lhs->elements) {
    if (elem->kind == ExprKind::kIdentifier && !elem->with_expr &&
        ctx.FindQueue(elem->text)) {
      // A bare dynamic queue triggers greedy sizing; leave that to the
      // established pass.
      return false;
    }
    if (elem->with_expr && elem->kind == ExprKind::kIdentifier &&
        ExprRefsIdentifierIn(elem->with_expr, earlier)) {
      dependency = true;
    }
    if (!elem->with_expr && elem->kind == ExprKind::kIdentifier &&
        !ctx.FindArrayInfo(elem->text) && !ctx.FindQueue(elem->text)) {
      earlier.push_back(elem->text);
    }
  }
  return dependency;
}

// Consumes the next `w` bits from the most-significant end of `rhs_val`, given
// that `cursor` bits have already been consumed. Out-of-range yields zeros.
using StreamTaker = std::function<Logic4Vec(uint32_t w)>;

// Forward-unpack arm for a fixed-array with-range element: write each selected
// element variable from successive stream bits, advancing `cursor`.
static void ForwardUnpackArrayWithRange(const Expr* elem, ArrayInfo* ainfo,
                                        SimContext& ctx, Arena& arena,
                                        const StreamTaker& take,
                                        uint32_t& cursor) {
  uint32_t start = 0, count = 0;
  bool in_range = ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size,
                                   ainfo->lo, start, count);
  if (!in_range || start + count > ainfo->size) {
    ctx.GetDiag().Error(
        {}, "streaming unpack with-range exceeds fixed array bounds");
    count = (start < ainfo->size) ? ainfo->size - start : 0;
  }
  for (uint32_t i = 0; i < count; ++i) {
    std::string name = std::string(elem->text) + "[" +
                       std::to_string(ainfo->lo + start + i) + "]";
    auto* var = ctx.FindVariable(name);
    if (!var)
      var = ctx.CreateVariable(*arena.Create<std::string>(name),
                               ainfo->elem_width);
    var->value = take(ainfo->elem_width);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
    cursor += ainfo->elem_width;
  }
}

// Forward-unpack arm for a queue with-range element: write each selected queue
// slot from successive stream bits, advancing `cursor`.
static void ForwardUnpackQueueWithRange(const Expr* elem, QueueObject* queue,
                                        SimContext& ctx, Arena& arena,
                                        const StreamTaker& take,
                                        uint32_t& cursor) {
  uint32_t start = 0, count = 0;
  ResolveWithRange(elem->with_expr, ctx, arena,
                   static_cast<uint32_t>(queue->elements.size()), 0, start,
                   count);
  uint32_t needed = start + count;
  while (queue->elements.size() < needed)
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  for (uint32_t i = 0; i < count; ++i) {
    Logic4Vec v = take(queue->elem_width);
    if (start + i < queue->elements.size()) queue->elements[start + i] = v;
    cursor += queue->elem_width;
  }
}

// Forward-unpack arm for a plain scalar/lvalue element: write the target from
// the next `width` stream bits, advancing `cursor`.
static void ForwardUnpackScalar(const Expr* elem, SimContext& ctx,
                                const StreamTaker& take, uint32_t& cursor) {
  auto* var = ResolveLhsVariable(elem, ctx);
  if (!var) return;
  uint32_t w = var->value.width;
  var->value = take(w);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
  cursor += w;
}

// Forward-unpack dispatch for one element (with-range array, with-range queue,
// or plain scalar/lvalue).
static void ForwardUnpackOneElement(const Expr* elem, SimContext& ctx,
                                    Arena& arena, const StreamTaker& take,
                                    uint32_t& cursor) {
  if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
    if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
      ForwardUnpackArrayWithRange(elem, ainfo, ctx, arena, take, cursor);
      return;
    }
    if (auto* queue = ctx.FindQueue(elem->text)) {
      ForwardUnpackQueueWithRange(elem, queue, ctx, arena, take, cursor);
      return;
    }
  }
  ForwardUnpackScalar(elem, ctx, take, cursor);
}

// Forward unpack for the right-shift form: walk elements in stream order and
// write each target before resolving the next element's with-range, consuming
// bits from the most-significant end of the stream as we go. This makes an
// earlier-unpacked field visible to a later array's with-range (§11.4.14.4).
static void UnpackStreamingConcatLhsForward(const Expr* lhs,
                                            const Logic4Vec& rhs_val,
                                            SimContext& ctx, Arena& arena) {
  uint32_t total = rhs_val.width;
  uint32_t cursor = 0;  // bits already consumed from the MSB end
  StreamTaker take = [&](uint32_t w) -> Logic4Vec {
    if (cursor + w <= total)
      return ExtractStreamBits(rhs_val, total - cursor - w, w, total, arena);
    return MakeLogic4Vec(arena, w);
  };
  for (auto* elem : lhs->elements) {
    ForwardUnpackOneElement(elem, ctx, arena, take, cursor);
  }
  if (cursor > total)
    ctx.GetDiag().Error({}, "too few bits in stream for streaming unpack");
}

// Produce a `total_width`-bit stream from `rhs_val`, dropping any surplus bits
// from the least-significant end (left-aligning the relevant bits).
static Logic4Vec BuildLeftAlignedStream(const Logic4Vec& rhs_val,
                                        uint32_t total_width, Arena& arena) {
  if (rhs_val.width <= total_width) return rhs_val;
  uint32_t shift = rhs_val.width - total_width;
  Logic4Vec stream = MakeLogic4Vec(arena, total_width);
  for (uint32_t b = 0; b < total_width; ++b) {
    CopyOneStreamBit(rhs_val, stream, shift + b, b);
  }
  return stream;
}

// Write `value` into `var`, coercing to 2-state if needed and notifying.
static void StoreStreamValueToVar(Variable* var, Logic4Vec value) {
  var->value = std::move(value);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

// Write a collected element targeting a synthetic queue slot
// ("<name>__q__<idx>") at `qpos`, the position of "__q__" in the name.
static void WriteStreamQueueElement(const StreamElemInfo& ei, size_t qpos,
                                    const Logic4Vec& stream,
                                    uint32_t bit_offset, uint32_t total_width,
                                    SimContext& ctx, Arena& arena) {
  auto qname = std::string_view(ei.target_name).substr(0, qpos);
  auto idx_str = ei.target_name.substr(qpos + 5);
  auto idx = static_cast<uint32_t>(std::stoul(idx_str));
  auto* queue = ctx.FindQueue(qname);
  if (queue && idx < queue->elements.size()) {
    queue->elements[idx] =
        ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
  }
}

// Write a collected element targeting a named variable, creating it on demand.
static void WriteStreamNamedVar(const StreamElemInfo& ei,
                                const Logic4Vec& stream, uint32_t bit_offset,
                                uint32_t total_width, SimContext& ctx,
                                Arena& arena) {
  auto* var = ctx.FindVariable(ei.target_name);
  if (!var) {
    var = ctx.CreateVariable(*arena.Create<std::string>(ei.target_name),
                             ei.width);
  }
  StoreStreamValueToVar(
      var, ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena));
}

// Write one collected stream element's bits to its target (queue slot, named
// variable, or resolved lvalue), coercing/notifying as needed.
static void WriteStreamElement(const StreamElemInfo& ei,
                               const Logic4Vec& stream, uint32_t bit_offset,
                               uint32_t total_width, SimContext& ctx,
                               Arena& arena) {
  if (!ei.target_name.empty()) {
    auto qpos = ei.target_name.find("__q__");
    if (qpos != std::string::npos) {
      WriteStreamQueueElement(ei, qpos, stream, bit_offset, total_width, ctx,
                              arena);
    } else {
      WriteStreamNamedVar(ei, stream, bit_offset, total_width, ctx, arena);
    }
    return;
  }
  auto* var = ResolveLhsVariable(ei.expr, ctx);
  if (!var) return;
  StoreStreamValueToVar(
      var, ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena));
}

void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  if (ShouldForwardResolveUnpack(lhs, ctx)) {
    UnpackStreamingConcatLhsForward(lhs, rhs_val, ctx, arena);
    return;
  }
  std::vector<StreamElemInfo> elems;
  uint32_t total_width =
      CollectStreamElements(lhs, ctx, arena, elems, rhs_val.width);
  if (total_width == 0 || elems.empty()) return;

  if (rhs_val.width < total_width) {
    ctx.GetDiag().Error({}, "too few bits in stream for streaming unpack");
    return;
  }

  Logic4Vec stream = BuildLeftAlignedStream(rhs_val, total_width, arena);

  if (lhs->op == TokenKind::kLtLt) {
    uint32_t ss = StreamSliceSizeForUnpack(lhs->lhs, ctx, arena);
    stream = ReverseStreamSlices(stream, total_width, ss, arena);
  }

  uint32_t bit_offset = total_width;
  for (auto& ei : elems) {
    bit_offset -= ei.width;
    WriteStreamElement(ei, stream, bit_offset, total_width, ctx, arena);
  }
}

}  // namespace delta
