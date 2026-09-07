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
#include "simulator/queue_bound.h"
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
    ctx.GetDiag().Error(size_expr->range.start,
                        "slice_size for streaming operator must be positive",
                        Subclause("11.4.14.2"));
    return 1;
  }
  return static_cast<uint32_t>(val);
}

struct StreamElemInfo {
  const Expr* expr;
  uint32_t width;
  std::string target_name;
};

// Streaming unpack evaluation environment (IEEE 1800 §11.4.14): the simulation
// context used to resolve/evaluate targets together with the arena used to
// allocate result vectors. These two always travel together.
struct StreamEnv {
  SimContext& ctx;
  Arena& arena;
};

// A source stream presented as a fixed-size bit buffer: the packed RHS value
// produced for the unpack plus its total bit width (the addressable bound).
struct StreamView {
  const Logic4Vec& stream;
  uint32_t total_width;
};

// Greedy-sizing budget for the single bare dynamic queue in an unpack target
// list (§11.4.14): the available RHS bit width and the bits already claimed by
// all fixed (non-greedy) targets. The greedy queue takes what remains.
struct GreedyFill {
  uint32_t rhs_width;
  uint32_t fixed_sum;
};

// The in-progress element collection for the greedy unpack pass: the growing
// list of collected stream targets, the running greedy-pass state (whether the
// one greedy dynamic queue has been consumed), and the per-call bits-added
// out-parameter.
struct GreedyUnpackSink {
  std::vector<StreamElemInfo>& elems;
  bool& first_dynamic_consumed;
  uint32_t& added;
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

// §11.4.14.3: a null class handle is skipped by the unpack operation — it
// consumes no stream bits, is left unmodified, and the unpack never allocates
// an object to fill (the hierarchy must be built before the streaming operator
// is applied). Detects a target element naming a class-handle variable that
// currently holds the null handle.
static bool IsNullClassHandleTarget(const Expr* elem, SimContext& ctx) {
  if (!elem || elem->kind != ExprKind::kIdentifier) return false;
  if (ctx.GetVariableClassType(elem->text).empty()) return false;
  auto* var = ctx.FindVariable(elem->text);
  return var && var->value.ToUint64() == kNullClassHandle;
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
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->with_expr, ctx, arena, {ainfo->size, ainfo->lo}, r);
    if (r.start + r.count > ainfo->size)
      r.count = (r.start < ainfo->size) ? ainfo->size - r.start : 0;
    return r.count * ainfo->elem_width;
  }
  if (auto* queue = ctx.FindQueue(elem->text)) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->with_expr, ctx, arena,
                     {static_cast<uint32_t>(queue->elements.size()), 0}, r);
    return r.count * queue->elem_width;
  }
  return 0;
}

// §11.4.14.1: "Each stream_expression within the stream_concatenation ... is
// converted to a bit-stream and appended", and Syntax 11-4 makes every item of
// a stream_concatenation an expression, so what a target element contributes is
// the expression's and not the object some sub-expression of it names. A select
// is such an element; a select with no base is not, its index standing on
// nothing to select from and the whole reducing to an ordinary lvalue. This is
// the test the plain-concatenation walk applies, for the same reason.
static bool IsStreamSelectElement(const Expr* elem) {
  return elem->kind == ExprKind::kSelect && elem->base != nullptr;
}

// §11.5.1: the bits a target element claims of the variable it resolved to --
// the window a select's indices address, and the whole variable for every other
// element shape.
//
// Reading the resolved variable's width for a select drew the boundary between
// elements in the wrong place: `{>> {a[3:0], b}} = 16'h9ABC` sized its first
// element at the whole of `a`, so the element to its right took the wrong bits
// too, giving `8'h9A` and `8'hBC` where §11.4.14.3 requires `8'hF9` and
// `8'hAB`; and it made an exactly fitting `12'h9AB` a 12-bit source against a
// 16-bit target list, rejected as too few bits in the stream.
//
// Three sites ask this question -- the collecting pass, the fixed-width sum the
// single greedy queue is budgeted from, and the forward pass -- and the writers
// deposit a select through WriteBitSelect, which resolves the same window, so
// the stream is carved and written on one boundary.
static uint32_t StreamElementClaimedBits(const Expr* elem, const Variable& var,
                                         SimContext& ctx, Arena& arena) {
  if (IsStreamSelectElement(elem))
    return SelectStorageBits(var, elem, ctx, arena).width;
  return var.value.width;
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
    // The budget the greedy queue is sized from is what the fixed elements
    // claim, so a select beside a queue contributes the bits it names; the
    // whole of its variable overstated the budget and left the queue short.
    if (var) fixed_sum += StreamElementClaimedBits(elem, *var, ctx, arena);
  }
  return fixed_sum;
}

// Collect targets for a fixed-array with-range element. Returns bits added.
static uint32_t CollectArrayWithRangeElements(
    const Expr* elem, ArrayInfo* ainfo, SimContext& ctx, Arena& arena,
    std::vector<StreamElemInfo>& elems) {
  StreamSliceRange r{0, 0};
  bool in_range = ResolveWithRange(elem->with_expr, ctx, arena,
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
  StreamSliceRange r{0, 0};
  ResolveWithRange(elem->with_expr, ctx, arena,
                   {static_cast<uint32_t>(queue->elements.size()), 0}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  uint32_t needed = start + count;
  while (queue->elements.size() < needed) {
    queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
  }
  // §7.10.3: the range names the elements this writes, so the elements outside
  // it are neither removed nor replaced and keep the identities any reference
  // to them was taken on. The elements grown onto the end are new and get
  // identities of their own.
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

// Collect targets for the (single) greedy dynamic queue, sized from the bits
// left after all fixed targets. Returns bits added.
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
  // §7.10.3: the queue is the whole target of the assignment, so every element
  // it held is gone and every reference to one of them is outdated.
  queue->AssignFreshIds();
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
static bool TryCollectGreedyDynamicElement(const Expr* elem, StreamEnv env,
                                           const GreedyFill& fill,
                                           const GreedyUnpackSink& sink) {
  if (elem->with_expr || elem->kind != ExprKind::kIdentifier) return false;
  auto* queue = env.ctx.FindQueue(elem->text);
  if (!queue) return false;
  if (!sink.first_dynamic_consumed) {
    sink.first_dynamic_consumed = true;
    sink.added =
        CollectGreedyQueueElements(elem, queue, fill, env.arena, sink.elems);
  } else {
    // §7.10.3: a second queue on the left of one streaming assignment takes no
    // bits and is emptied, which removes every element it held and so outdates
    // every reference to one.
    queue->elements.clear();
    queue->element_ids.clear();
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
        TryCollectGreedyDynamicElement(
            elem, StreamEnv{ctx, arena}, GreedyFill{rhs_width, fixed_sum},
            GreedyUnpackSink{elems, first_dynamic_consumed, added})) {
      total_width += added;
      continue;
    }
    // §11.4.14.3: a null class handle target is skipped (no bits consumed, not
    // modified, no object created).
    if (IsNullClassHandleTarget(elem, ctx)) continue;
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    uint32_t width = StreamElementClaimedBits(elem, *var, ctx, arena);
    elems.push_back({elem, width, {}});
    total_width += width;
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
                                        StreamEnv env, const StreamTaker& take,
                                        uint32_t& cursor) {
  StreamSliceRange r{0, 0};
  bool in_range = ResolveWithRange(elem->with_expr, env.ctx, env.arena,
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
    std::string name = std::string(elem->text) + "[" +
                       std::to_string(ainfo->lo + start + i) + "]";
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

// Forward-unpack arm for a queue with-range element: write each selected queue
// slot from successive stream bits, advancing `cursor`.
static void ForwardUnpackQueueWithRange(const Expr* elem, QueueObject* queue,
                                        StreamEnv env, const StreamTaker& take,
                                        uint32_t& cursor) {
  StreamSliceRange r{0, 0};
  ResolveWithRange(elem->with_expr, env.ctx, env.arena,
                   {static_cast<uint32_t>(queue->elements.size()), 0}, r);
  uint32_t start = r.start;
  uint32_t count = r.count;
  uint32_t needed = start + count;
  while (queue->elements.size() < needed)
    queue->elements.push_back(MakeLogic4Vec(env.arena, queue->elem_width));
  // §7.10.3: as in CollectQueueWithRangeElements, growing the queue removes
  // nothing, so the elements already there keep their identities and only the
  // new ones are given any.
  queue->AllocateIdsForAppended();
  for (uint32_t i = 0; i < count; ++i) {
    Logic4Vec v = take(queue->elem_width);
    if (start + i < queue->elements.size()) queue->elements[start + i] = v;
    cursor += queue->elem_width;
  }
}

// Forward-unpack arm for a plain scalar/lvalue element: write the target from
// the next `width` stream bits, advancing `cursor`.
static void ForwardUnpackScalar(const Expr* elem, StreamEnv env,
                                const StreamTaker& take, uint32_t& cursor) {
  auto* var = ResolveLhsVariable(elem, env.ctx);
  if (!var) return;
  uint32_t w = StreamElementClaimedBits(elem, *var, env.ctx, env.arena);
  Logic4Vec bits = take(w);
  // §11.4.14.3 unpacks the stream "into one or more variables", and a select
  // element names a window of a variable rather than the variable, so the bits
  // outside it stand. WriteBitSelect resolves the window the width above was
  // measured over, which is what keeps this pass's consumption and its writes
  // on one boundary.
  if (IsStreamSelectElement(elem)) {
    WriteBitSelect(var, elem, bits, env.ctx, env.arena);
  } else {
    var->value = bits;
    if (!var->is_4state) CoerceTo2State(var->value);
  }
  var->NotifyWatchers();
  cursor += w;
}

// Forward-unpack dispatch for one element (with-range array, with-range queue,
// or plain scalar/lvalue).
static void ForwardUnpackOneElement(const Expr* elem, SimContext& ctx,
                                    Arena& arena, const StreamTaker& take,
                                    uint32_t& cursor) {
  // §11.4.14.3: a null class handle target is skipped, consuming no bits.
  if (IsNullClassHandleTarget(elem, ctx)) return;
  if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
    if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
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
    ctx.GetDiag().Error(lhs->range.start,
                        "too few bits in stream for streaming unpack",
                        Subclause("11.4.14.3"));
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
  var->value = value;
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

// Write a collected element targeting a synthetic queue slot
// ("<name>__q__<idx>") at `qpos`, the position of "__q__" in the name.
static void WriteStreamQueueElement(const StreamElemInfo& ei, size_t qpos,
                                    const StreamView& src, uint32_t bit_offset,
                                    StreamEnv env) {
  auto qname = std::string_view(ei.target_name).substr(0, qpos);
  auto idx_str = ei.target_name.substr(qpos + 5);
  auto idx = static_cast<uint32_t>(std::stoul(idx_str));
  auto* queue = env.ctx.FindQueue(qname);
  if (queue && idx < queue->elements.size()) {
    queue->elements[idx] = ExtractStreamBits(src.stream, bit_offset, ei.width,
                                             src.total_width, env.arena);
  }
}

// Write a collected element targeting a named variable, creating it on demand.
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

// Write one collected stream element's bits to its target (queue slot, named
// variable, or resolved lvalue), coercing/notifying as needed.
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
  // §11.4.14.3 deposits an element's bits in what the element names, and a
  // select names a window of its variable, so the rest of that variable stands;
  // storing the value whole gave `{>> {a[3:0], b}}` the whole of `a` and lost
  // the bits `a[7:4]` had. WriteBitSelect resolves the same window
  // StreamElementClaimedBits measured, so the stream is carved and deposited on
  // one boundary. It also declines a variable §10.6.2 has forced, which
  // StoreStreamValueToVar does not test.
  if (IsStreamSelectElement(ei.expr)) {
    WriteBitSelect(var, ei.expr, bits, env.ctx, env.arena);
    var->NotifyWatchers();
    return;
  }
  StoreStreamValueToVar(var, bits);
}

// §7.10.5: an unpack grows a queue target to the slots its with-range names or
// to the elements the leftover bits fill, and the bound applies to what the
// whole unpack leaves behind rather than to each element as it arrives. Every
// queue the target list names is therefore trimmed once the unpack has run.
static void EnforceQueueTargetBounds(const Expr* lhs, SimContext& ctx) {
  for (const auto* elem : lhs->elements) {
    if (!elem || elem->kind != ExprKind::kIdentifier) continue;
    if (auto* queue = ctx.FindQueue(elem->text))
      EnforceQueueBound(queue, "streaming assignment", elem->range.start, ctx);
  }
}

void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena) {
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
    uint32_t ss = StreamSliceSizeForUnpack(lhs->lhs, ctx, arena);
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

// §11.4.14: extract a slice of `total_w` bits from `src` starting at bit
// `start`, returning a `width`-bit Logic4Vec. Helper shared by the
// pack-to-queue path below.
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

// §11.4.14: handle a streaming_concatenation feeding a dynamically sized
// target. Resize the target to the smallest number of elements that is at
// least as wide as the stream; if the resized total exceeds the stream width,
// pad the stream with zero bits on the right before unpacking.
// Left-shift `stream` (stream_w bits) into a `total_w`-bit vector, padding the
// LSB side with zero bits. When no padding is needed the input is returned.
static Logic4Vec RightPadStreamToWidth(const Logic4Vec& stream,
                                       uint32_t stream_w, uint32_t total_w,
                                       Arena& arena) {
  if (total_w <= stream_w) return stream;
  auto widened = MakeLogic4Vec(arena, total_w);
  uint32_t shift = total_w - stream_w;
  for (uint32_t b = 0; b < stream_w; ++b) {
    uint32_t sw = b / 64, sb = b % 64;
    uint32_t dst_bit = shift + b;
    uint32_t dw = dst_bit / 64, db = dst_bit % 64;
    if (sw < stream.nwords) {
      if ((stream.words[sw].aval >> sb) & 1ull)
        widened.words[dw].aval |= uint64_t{1} << db;
      if ((stream.words[sw].bval >> sb) & 1ull)
        widened.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return widened;
}

// §11.4.14: geometry of a widened bit-stream that is unpacked MSB-first into a
// queue: the padded stream bits plus the element count, total width, and
// element width describing how to carve it into successive elements.
struct WidenedStreamLayout {
  const Logic4Vec& widened;
  uint32_t n_elems;
  uint32_t total_w;
  uint32_t elem_w;
};

// Repopulate `queue` from the widened stream described by `layout`, carving out
// `n_elems` element-width slices (MSB-first into successive elements).
static void PopulateQueueFromWidenedStream(QueueObject* queue,
                                           const WidenedStreamLayout& layout,
                                           Arena& arena) {
  queue->elements.clear();
  queue->elements.reserve(layout.n_elems);
  for (uint32_t i = 0; i < layout.n_elems; ++i) {
    uint32_t src_start = layout.total_w - (i + 1) * layout.elem_w;
    queue->elements.push_back(
        ExtractWidenedSlice(layout.widened, src_start, layout.elem_w, arena));
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

// §11.4.14: when a streaming_concatenation is the source of an assignment and
// the target is a data object of bit-stream type, the stream is left-aligned
// in the target. A fixed-size target wider than the stream is filled with
// zero bits on the right (LSB side); a fixed-size target narrower than the
// stream is an error.
Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kStreamingConcat) {
    return rhs_val;
  }
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return rhs_val;
  }
  if (ctx.FindArrayInfo(stmt->lhs->text) || ctx.FindQueue(stmt->lhs->text) ||
      ctx.FindAssocArray(stmt->lhs->text)) {
    return rhs_val;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var || var->value.width == 0) return rhs_val;
  uint32_t target_width = var->value.width;
  uint32_t stream_width = rhs_val.width;
  if (target_width == stream_width) return rhs_val;
  if (target_width < stream_width) {
    ctx.GetDiag().Error(
        stmt->lhs->range.start,
        "streaming concatenation source is wider than the fixed-size target",
        Subclause("11.4.14"));
    return rhs_val;
  }

  return RightPadStreamToWidth(rhs_val, stream_width, target_width, arena);
}

}  // namespace delta
