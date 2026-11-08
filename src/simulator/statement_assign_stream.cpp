#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

struct StreamElemInfo {
  const Expr* expr;
  uint32_t width;
  std::string target_name;
};

struct StreamEnv {
  SimContext& ctx;
  Arena& arena;
};

struct StreamView {
  const Logic4Vec& stream;
  uint32_t total_width;
};

struct GreedyFill {
  uint32_t rhs_width;
  uint32_t fixed_sum;
};

struct GreedyUnpackSink {
  std::vector<StreamElemInfo>& elems;
  bool& first_dynamic_consumed;
  uint32_t& added;
};

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

static void ResolvePlusPartSelectRange(int64_t idx, int64_t idx2,
                                       uint32_t array_lo, uint32_t& out_start,
                                       uint32_t& out_count) {
  int64_t rel = idx - static_cast<int64_t>(array_lo);
  out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
  out_count = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
}

static void ResolveMinusPartSelectRange(int64_t idx, int64_t idx2,
                                        uint32_t array_lo, uint32_t& out_start,
                                        uint32_t& out_count) {
  uint32_t width = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
  int64_t lo_idx = idx - static_cast<int64_t>(width) + 1;
  int64_t rel = lo_idx - static_cast<int64_t>(array_lo);
  out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
  out_count = width;
}

static void ResolveExplicitRange(int64_t idx, int64_t idx2, uint32_t array_lo,
                                 uint32_t& out_start, uint32_t& out_count) {
  int64_t lo = idx, hi = idx2;
  if (lo > hi) std::swap(lo, hi);
  int64_t rel_lo = lo - static_cast<int64_t>(array_lo);
  out_start = (rel_lo < 0) ? 0 : static_cast<uint32_t>(rel_lo);
  out_count = static_cast<uint32_t>(hi - lo + 1);
}

bool ResolveWithRange(const Expr* with_expr, SimContext& ctx, Arena& arena,
                      ArrayGeom geom, StreamSliceRange& out_range) {
  uint32_t& out_start = out_range.start;
  uint32_t& out_count = out_range.count;
  if (!with_expr || with_expr->kind != ExprKind::kSelect) {
    out_start = 0;
    out_count = geom.size;
    return true;
  }
  int64_t idx =
      static_cast<int64_t>(EvalExpr(with_expr->index, ctx, arena).ToUint64());
  if (!with_expr->index_end) {
    return ResolveSingleIndexRange(idx, geom.size, geom.lo, out_start,
                                   out_count);
  }
  int64_t idx2 = static_cast<int64_t>(
      EvalExpr(with_expr->index_end, ctx, arena).ToUint64());
  if (with_expr->is_part_select_plus) {
    ResolvePlusPartSelectRange(idx, idx2, geom.lo, out_start, out_count);
  } else if (with_expr->is_part_select_minus) {
    ResolveMinusPartSelectRange(idx, idx2, geom.lo, out_start, out_count);
  } else {
    ResolveExplicitRange(idx, idx2, geom.lo, out_start, out_count);
  }
  return true;
}

static bool IsNullClassHandleTarget(const Expr* elem, SimContext& ctx) {
  if (!elem || elem->kind != ExprKind::kIdentifier) return false;
  if (ctx.GetVariableClassType(elem->text).empty()) return false;
  auto* var = ctx.FindVariable(elem->text);
  return var && var->value.ToUint64() == kNullClassHandle;
}

static bool LhsHasGreedyDynamicElement(const Expr* lhs, SimContext& ctx) {
  for (auto* elem : lhs->elements) {
    if (elem->stream_range) continue;
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text)) {
      return true;
    }
  }
  return false;
}

static uint32_t FixedWithRangeElementWidth(const Expr* elem, SimContext& ctx,
                                           Arena& arena) {
  if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->stream_range, ctx, arena, {ainfo->size, ainfo->lo},
                     r);
    if (r.start + r.count > ainfo->size)
      r.count = (r.start < ainfo->size) ? ainfo->size - r.start : 0;
    return r.count * ainfo->elem_width;
  }
  if (auto* queue = ctx.FindQueue(elem->text)) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->stream_range, ctx, arena,
                     {static_cast<uint32_t>(queue->elements.size()), 0}, r);
    return r.count * queue->elem_width;
  }
  return 0;
}

static bool IsStreamSelectElement(const Expr* elem) {
  return elem->kind == ExprKind::kSelect && elem->base != nullptr;
}

static uint32_t StreamElementClaimedBits(const Expr* elem, const Variable& var,
                                         SimContext& ctx, Arena& arena) {
  if (IsStreamSelectElement(elem))
    return SelectExprWidth(var, elem, ctx, arena);
  return var.value.width;
}

static uint32_t SumFixedElementWidths(const Expr* lhs, SimContext& ctx,
                                      Arena& arena) {
  uint32_t fixed_sum = 0;
  for (auto* elem : lhs->elements) {
    if (elem->stream_range && elem->kind == ExprKind::kIdentifier) {
      fixed_sum += FixedWithRangeElementWidth(elem, ctx, arena);
      continue;
    }
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text))
      continue;
    auto* var = ResolveLhsVariable(elem, ctx);
    if (var) fixed_sum += StreamElementClaimedBits(elem, *var, ctx, arena);
  }
  return fixed_sum;
}

static uint32_t CollectArrayWithRangeElements(
    const Expr* elem, ArrayInfo* ainfo, SimContext& ctx, Arena& arena,
    std::vector<StreamElemInfo>& elems) {
  StreamSliceRange r{0, 0};
  bool in_range = ResolveWithRange(elem->stream_range, ctx, arena,
                                   {ainfo->size, ainfo->lo}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  if (!in_range || start + count > ainfo->size) {
    uint32_t clamped = (start < ainfo->size) ? ainfo->size - start : 0;
    ctx.GetDiag().Error(
        elem->range.start,
        "streaming unpack with-range exceeds fixed array bounds",
        Subclause("11.4.14.4"));
    count = clamped;
  }
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t abs_idx =
        ainfo->lo + (ainfo->is_descending ? start + count - 1 - i : start + i);
    std::string name =
        std::string(elem->text) + "[" + std::to_string(abs_idx) + "]";
    elems.push_back({elem, ainfo->elem_width, std::move(name)});
    added += ainfo->elem_width;
  }
  return added;
}

static uint32_t CollectQueueWithRangeElements(
    const Expr* elem, QueueObject* queue, SimContext& ctx, Arena& arena,
    std::vector<StreamElemInfo>& elems) {
  StreamSliceRange r{0, 0};
  ResolveWithRange(elem->stream_range, ctx, arena,
                   {static_cast<uint32_t>(queue->elements.size()), 0}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  uint32_t needed = start + count;
  while (queue->elements.size() < needed) {
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  }
  queue->AllocateIdsForAppended();
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    std::string name =
        std::string(elem->text) + "__q__" + std::to_string(start + i);
    elems.push_back({elem, queue->elem_width, std::move(name)});
    added += queue->elem_width;
  }
  return added;
}

static uint32_t CollectGreedyQueueElements(const Expr* elem, QueueObject* queue,
                                           const GreedyFill& fill, Arena& arena,
                                           std::vector<StreamElemInfo>& elems) {
  uint32_t remaining =
      (fill.rhs_width > fill.fixed_sum) ? fill.rhs_width - fill.fixed_sum : 0;
  uint32_t count = queue->elem_width > 0 ? remaining / queue->elem_width : 0;
  queue->elements.clear();
  for (uint32_t i = 0; i < count; ++i) {
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  }
  queue->AssignFreshIds();
  uint32_t added = 0;
  for (uint32_t i = 0; i < count; ++i) {
    std::string name = std::string(elem->text) + "__q__" + std::to_string(i);
    elems.push_back({elem, queue->elem_width, std::move(name)});
    added += queue->elem_width;
  }
  return added;
}

static bool TryCollectWithRangeElement(const Expr* elem, SimContext& ctx,
                                       Arena& arena,
                                       std::vector<StreamElemInfo>& elems,
                                       uint32_t& added) {
  if (!elem->stream_range || elem->kind != ExprKind::kIdentifier) return false;
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

static bool TryCollectGreedyDynamicElement(const Expr* elem, StreamEnv env,
                                           const GreedyFill& fill,
                                           const GreedyUnpackSink& sink) {
  if (elem->stream_range || elem->kind != ExprKind::kIdentifier) return false;
  auto* queue = env.ctx.FindQueue(elem->text);
  if (!queue) return false;
  if (!sink.first_dynamic_consumed) {
    sink.first_dynamic_consumed = true;
    sink.added =
        CollectGreedyQueueElements(elem, queue, fill, env.arena, sink.elems);
  } else {
    queue->elements.clear();
    queue->element_ids.clear();
  }
  return true;
}

static bool TryCollectFixedArrayElements(const Expr* elem, SimContext& ctx,
                                         std::vector<StreamElemInfo>& elems,
                                         uint32_t& added) {
  if (elem->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* ainfo = ctx.FindArrayInfo(elem->text);
  if (ainfo == nullptr || ainfo->is_dynamic) return false;
  std::vector<std::string> suffixes = MultiDimLeafSuffixes(*ainfo);
  const bool kOneDimension = suffixes.empty();
  for (uint32_t i = 0; kOneDimension && i < ainfo->size; ++i) {
    const uint32_t kOffset = ainfo->is_descending ? ainfo->size - 1 - i : i;
    suffixes.push_back("[" + std::to_string(ainfo->lo + kOffset) + "]");
  }
  for (const std::string& suffix : suffixes) {
    elems.push_back(
        {elem, ainfo->elem_width, std::string(elem->text) + suffix});
    added += ainfo->elem_width;
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
    if (TryCollectWithRangeElement(elem, ctx, arena, elems, added) ||
        TryCollectFixedArrayElements(elem, ctx, elems, added)) {
      total_width += added;
      continue;
    }
    if (has_dynamic &&
        TryCollectGreedyDynamicElement(
            elem, StreamEnv{ctx, arena}, GreedyFill{rhs_width, fixed_sum},
            GreedyUnpackSink{elems, first_dynamic_consumed, added})) {
      total_width += added;
      continue;
    }
    if (IsNullClassHandleTarget(elem, ctx)) continue;
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    uint32_t width = StreamElementClaimedBits(elem, *var, ctx, arena);
    elems.push_back({elem, width, {}});
    total_width += width;
  }
  return total_width;
}

static void CopyOneStreamBit(const Logic4Vec& src, Logic4Vec& dst,
                             uint32_t sbit, uint32_t dbit) {
  uint32_t sw = sbit / 64, sb = sbit % 64;
  uint32_t dw = dbit / 64, db = dbit % 64;
  if (sw >= src.nwords) return;
  if ((src.words[sw].aval >> sb) & 1) dst.words[dw].aval |= uint64_t{1} << db;
  if ((src.words[sw].bval >> sb) & 1) dst.words[dw].bval |= uint64_t{1} << db;
}

static void CopyStreamSliceBits(const StreamView& src, Logic4Vec& dst,
                                uint32_t src_start, uint32_t dst_start,
                                uint32_t bits_to_copy) {
  for (uint32_t b = 0; b < bits_to_copy; ++b) {
    uint32_t dbit = dst_start + b;
    if (dbit >= src.total_width) break;
    CopyOneStreamBit(src.stream, dst, src_start + b, dbit);
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
    CopyStreamSliceBits(StreamView{stream, total_width}, reordered, src_start,
                        dst_start, bits_to_copy);
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

static bool ShouldForwardResolveUnpack(const Expr* lhs, SimContext& ctx) {
  std::vector<std::string_view> earlier;
  bool dependency = false;
  for (auto* elem : lhs->elements) {
    if (elem->kind == ExprKind::kIdentifier && !elem->stream_range &&
        ctx.FindQueue(elem->text)) {
      return false;
    }
    if (elem->stream_range && elem->kind == ExprKind::kIdentifier &&
        ExprRefsIdentifierIn(elem->stream_range, earlier)) {
      dependency = true;
    }
    if (!elem->stream_range && elem->kind == ExprKind::kIdentifier &&
        !ctx.FindArrayInfo(elem->text) && !ctx.FindQueue(elem->text)) {
      earlier.push_back(elem->text);
    }
  }
  return dependency;
}

using StreamTaker = std::function<Logic4Vec(uint32_t w)>;

static void ForwardUnpackArrayWithRange(const Expr* elem, ArrayInfo* ainfo,
                                        StreamEnv env, const StreamTaker& take,
                                        uint32_t& cursor) {
  StreamSliceRange r{0, 0};
  bool in_range = ResolveWithRange(elem->stream_range, env.ctx, env.arena,
                                   {ainfo->size, ainfo->lo}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  if (!in_range || start + count > ainfo->size) {
    env.ctx.GetDiag().Error(
        elem->range.start,
        "streaming unpack with-range exceeds fixed array bounds",
        Subclause("11.4.14.4"));
    count = (start < ainfo->size) ? ainfo->size - start : 0;
  }
  for (uint32_t i = 0; i < count; ++i) {
    std::string name =
        std::string(elem->text) + "[" +
        std::to_string(ainfo->lo + (ainfo->is_descending ? start + count - 1 - i
                                                         : start + i)) +
        "]";
    auto* var = env.ctx.FindVariable(name);
    if (!var)
      var = env.ctx.CreateVariable(*env.arena.Create<std::string>(name),
                                   ainfo->elem_width);
    var->value = take(ainfo->elem_width);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
    cursor += ainfo->elem_width;
  }
}

static Logic4Vec AsQueueElement(const QueueObject& queue, Logic4Vec value) {
  if (!queue.is_4state) CoerceTo2State(value);
  return value;
}

static void ForwardUnpackQueueWithRange(const Expr* elem, QueueObject* queue,
                                        StreamEnv env, const StreamTaker& take,
                                        uint32_t& cursor) {
  StreamSliceRange r{0, 0};
  ResolveWithRange(elem->stream_range, env.ctx, env.arena,
                   {static_cast<uint32_t>(queue->elements.size()), 0}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  uint32_t needed = start + count;
  while (queue->elements.size() < needed)
    queue->elements.push_back(MakeLogic4Vec(env.arena, queue->elem_width));
  queue->AllocateIdsForAppended();
  for (uint32_t i = 0; i < count; ++i) {
    Logic4Vec v = take(queue->elem_width);
    if (start + i < queue->elements.size())
      queue->elements[start + i] = AsQueueElement(*queue, v);
    cursor += queue->elem_width;
  }
}

static void StoreStreamValueToVar(Variable* var, Logic4Vec value);

static void ForwardUnpackScalar(const Expr* elem, StreamEnv env,
                                const StreamTaker& take, uint32_t& cursor) {
  auto* var = ResolveLhsVariable(elem, env.ctx);
  if (!var) return;
  uint32_t w = StreamElementClaimedBits(elem, *var, env.ctx, env.arena);
  Logic4Vec bits = take(w);
  if (IsStreamSelectElement(elem)) {
    WriteBitSelect(var, elem, bits, env.ctx, env.arena);
  } else {
    StoreStreamValueToVar(var, bits);
  }
  cursor += w;
}

static void ForwardUnpackOneElement(const Expr* elem, SimContext& ctx,
                                    Arena& arena, const StreamTaker& take,
                                    uint32_t& cursor) {
  if (IsNullClassHandleTarget(elem, ctx)) return;
  if (elem->stream_range && elem->kind == ExprKind::kIdentifier) {
    if (auto* ainfo = ctx.FindArrayInfo(elem->text);
        ainfo != nullptr && !ainfo->is_dynamic) {
      ForwardUnpackArrayWithRange(elem, ainfo, StreamEnv{ctx, arena}, take,
                                  cursor);
      return;
    }
    if (auto* queue = ctx.FindQueue(elem->text)) {
      ForwardUnpackQueueWithRange(elem, queue, StreamEnv{ctx, arena}, take,
                                  cursor);
      return;
    }
  }
  ForwardUnpackScalar(elem, StreamEnv{ctx, arena}, take, cursor);
}

static void UnpackStreamingConcatLhsForward(const Expr* lhs,
                                            const Logic4Vec& rhs_val,
                                            SimContext& ctx, Arena& arena) {
  uint32_t total = rhs_val.width;
  Logic4Vec stream = rhs_val;
  if (lhs->op == TokenKind::kLtLt) {
    uint32_t ss = StreamSliceSize(lhs->lhs, ctx, arena);
    stream = ReverseStreamSlices(rhs_val, total, ss, arena);
  }
  uint32_t cursor = 0;
  StreamTaker take = [&](uint32_t w) -> Logic4Vec {
    if (cursor + w <= total)
      return ExtractStreamBits(stream, total - cursor - w, w, total, arena);
    return MakeLogic4Vec(arena, w);
  };
  for (auto* elem : lhs->elements) {
    ForwardUnpackOneElement(elem, ctx, arena, take, cursor);
  }
  if (cursor > total)
    ctx.GetDiag().Error(lhs->range.start,
                        "too few bits in stream for streaming unpack",
                        Subclause("11.4.14.3"));
}

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

static void StoreStreamValueToVar(Variable* var, Logic4Vec value) {
  if (var->is_forced) return;
  var->value = value;
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

static void WriteStreamQueueElement(const StreamElemInfo& ei, size_t qpos,
                                    const StreamView& src, uint32_t bit_offset,
                                    StreamEnv env) {
  auto qname = std::string_view(ei.target_name).substr(0, qpos);
  auto idx_str = ei.target_name.substr(qpos + 5);
  auto idx = static_cast<uint32_t>(std::stoul(idx_str));
  auto* queue = env.ctx.FindQueue(qname);
  if (queue && idx < queue->elements.size()) {
    queue->elements[idx] = AsQueueElement(
        *queue, ExtractStreamBits(src.stream, bit_offset, ei.width,
                                  src.total_width, env.arena));
  }
}

static void WriteStreamNamedVar(const StreamElemInfo& ei, const StreamView& src,
                                uint32_t bit_offset, StreamEnv env) {
  auto* var = env.ctx.FindVariable(ei.target_name);
  if (!var) {
    var = env.ctx.CreateVariable(*env.arena.Create<std::string>(ei.target_name),
                                 ei.width);
  }
  StoreStreamValueToVar(var, ExtractStreamBits(src.stream, bit_offset, ei.width,
                                               src.total_width, env.arena));
}

static void WriteStreamElement(const StreamElemInfo& ei, const StreamView& src,
                               uint32_t bit_offset, StreamEnv env) {
  if (!ei.target_name.empty()) {
    auto qpos = ei.target_name.find("__q__");
    if (qpos != std::string::npos) {
      WriteStreamQueueElement(ei, qpos, src, bit_offset, env);
    } else {
      WriteStreamNamedVar(ei, src, bit_offset, env);
    }
    return;
  }
  auto* var = ResolveLhsVariable(ei.expr, env.ctx);
  if (!var) return;
  Logic4Vec bits = ExtractStreamBits(src.stream, bit_offset, ei.width,
                                     src.total_width, env.arena);
  if (IsStreamSelectElement(ei.expr)) {
    WriteBitSelect(var, ei.expr, bits, env.ctx, env.arena);
    return;
  }
  StoreStreamValueToVar(var, bits);
}

static void EnforceQueueTargetBounds(const Expr* lhs, SimContext& ctx) {
  for (const auto* elem : lhs->elements) {
    if (!elem || elem->kind != ExprKind::kIdentifier) continue;
    if (auto* queue = ctx.FindQueue(elem->text))
      EnforceQueueBound(queue, "streaming assignment", elem->range.start, ctx);
  }
}

void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
  if (TryUnpackStreamIntoProperties(lhs, rhs_val, ctx, arena)) return;
  if (ShouldForwardResolveUnpack(lhs, ctx)) {
    UnpackStreamingConcatLhsForward(lhs, rhs_val, ctx, arena);
    EnforceQueueTargetBounds(lhs, ctx);
    return;
  }
  std::vector<StreamElemInfo> elems;
  uint32_t total_width =
      CollectStreamElements(lhs, ctx, arena, elems, rhs_val.width);
  if (total_width == 0 || elems.empty()) return;

  if (rhs_val.width < total_width) {
    ctx.GetDiag().Error(lhs->range.start,
                        "too few bits in stream for streaming unpack",
                        Subclause("11.4.14.3"));
    return;
  }

  Logic4Vec stream = BuildLeftAlignedStream(rhs_val, total_width, arena);

  if (lhs->op == TokenKind::kLtLt) {
    uint32_t ss = StreamSliceSize(lhs->lhs, ctx, arena);
    stream = ReverseStreamSlices(stream, total_width, ss, arena);
  }

  uint32_t bit_offset = total_width;
  StreamView src{stream, total_width};
  for (auto& ei : elems) {
    bit_offset -= ei.width;
    WriteStreamElement(ei, src, bit_offset, StreamEnv{ctx, arena});
  }
  EnforceQueueTargetBounds(lhs, ctx);
}

static Logic4Vec ExtractWidenedSlice(const Logic4Vec& src, uint32_t start,
                                     uint32_t width, Arena& arena) {
  auto out = MakeLogic4Vec(arena, width);
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t sbit = start + b;
    uint32_t sw = sbit / 64, sb = sbit % 64;
    uint32_t dw = b / 64, db = b % 64;
    if (sw < src.nwords) {
      if ((src.words[sw].aval >> sb) & 1ull)
        out.words[dw].aval |= uint64_t{1} << db;
      if ((src.words[sw].bval >> sb) & 1ull)
        out.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return out;
}

struct WidenedStreamLayout {
  const Logic4Vec& widened;
  uint32_t n_elems;
  uint32_t total_w;
  uint32_t elem_w;
};

static void PopulateQueueFromWidenedStream(QueueObject* queue,
                                           const WidenedStreamLayout& layout,
                                           Arena& arena) {
  queue->elements.clear();
  queue->elements.reserve(layout.n_elems);
  for (uint32_t i = 0; i < layout.n_elems; ++i) {
    uint32_t src_start = layout.total_w - (i + 1) * layout.elem_w;
    queue->elements.push_back(AsQueueElement(
        *queue,
        ExtractWidenedSlice(layout.widened, src_start, layout.elem_w, arena)));
  }
  queue->AssignFreshIds();
  ++queue->generation;
}

bool TryStreamingConcatToQueueTarget(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kStreamingConcat) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* queue = ctx.FindQueue(stmt->lhs->text);
  if (!queue) return false;

  auto stream = EvalExpr(stmt->rhs, ctx, arena);
  uint32_t stream_w = stream.width;
  uint32_t elem_w = queue->elem_width;
  if (elem_w == 0) return false;

  if (stream_w == 0) {
    queue->elements.clear();
    queue->element_ids.clear();
    ++queue->generation;
    return true;
  }

  uint32_t n_elems = (stream_w + elem_w - 1) / elem_w;
  uint32_t total_w = n_elems * elem_w;

  Logic4Vec widened = RightPadStreamToWidth(stream, stream_w, total_w, arena);
  PopulateQueueFromWidenedStream(
      queue, WidenedStreamLayout{widened, n_elems, total_w, elem_w}, arena);
  EnforceQueueBound(queue, "streaming assignment", stmt->rhs->range.start, ctx);
  return true;
}

}  // namespace delta
