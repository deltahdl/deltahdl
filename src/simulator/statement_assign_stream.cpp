#include <algorithm>
#include <cstdint>
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
  int64_t idx2 = static_cast<int64_t>(
      EvalExpr(with_expr->index_end, ctx, arena).ToUint64());
  if (with_expr->is_part_select_plus) {
    int64_t rel = idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
  } else if (with_expr->is_part_select_minus) {
    uint32_t width = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
    int64_t lo_idx = idx - static_cast<int64_t>(width) + 1;
    int64_t rel = lo_idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = width;
  } else {
    int64_t lo = idx, hi = idx2;
    if (lo > hi) std::swap(lo, hi);
    int64_t rel_lo = lo - static_cast<int64_t>(array_lo);
    out_start = (rel_lo < 0) ? 0 : static_cast<uint32_t>(rel_lo);
    out_count = static_cast<uint32_t>(hi - lo + 1);
  }
  return true;
}

static uint32_t CollectStreamElements(const Expr* lhs, SimContext& ctx,
                                      Arena& arena,
                                      std::vector<StreamElemInfo>& elems,
                                      uint32_t rhs_width) {
  bool has_dynamic = false;
  for (auto* elem : lhs->elements) {
    if (elem->with_expr) continue;
    if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text)) {
      has_dynamic = true;
      break;
    }
  }

  uint32_t fixed_sum = 0;
  if (has_dynamic) {
    for (auto* elem : lhs->elements) {
      if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
        if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
          uint32_t start = 0, count = 0;
          ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size, ainfo->lo,
                           start, count);
          if (start + count > ainfo->size)
            count = (start < ainfo->size) ? ainfo->size - start : 0;
          fixed_sum += count * ainfo->elem_width;
        } else if (auto* queue = ctx.FindQueue(elem->text)) {
          uint32_t start = 0, count = 0;
          ResolveWithRange(elem->with_expr, ctx, arena,
                           static_cast<uint32_t>(queue->elements.size()), 0,
                           start, count);
          fixed_sum += count * queue->elem_width;
        }
        continue;
      }
      if (elem->kind == ExprKind::kIdentifier && ctx.FindQueue(elem->text))
        continue;
      auto* var = ResolveLhsVariable(elem, ctx);
      if (var) fixed_sum += var->value.width;
    }
  }

  uint32_t total_width = 0;
  bool first_dynamic_consumed = false;
  for (auto* elem : lhs->elements) {
    if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
      if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
        uint32_t start = 0, count = 0;
        bool in_range = ResolveWithRange(elem->with_expr, ctx, arena,
                                         ainfo->size, ainfo->lo, start, count);
        if (!in_range || start + count > ainfo->size) {
          uint32_t clamped = (start < ainfo->size) ? ainfo->size - start : 0;
          ctx.GetDiag().Error(
              {}, "streaming unpack with-range exceeds fixed array bounds");
          count = clamped;
        }
        for (uint32_t i = 0; i < count; ++i) {
          uint32_t abs_idx = ainfo->lo + start + i;
          std::string name =
              std::string(elem->text) + "[" + std::to_string(abs_idx) + "]";
          elems.push_back({elem, ainfo->elem_width, std::move(name)});
          total_width += ainfo->elem_width;
        }
        continue;
      }
      if (auto* queue = ctx.FindQueue(elem->text)) {
        uint32_t start = 0, count = 0;
        ResolveWithRange(elem->with_expr, ctx, arena,
                         static_cast<uint32_t>(queue->elements.size()), 0,
                         start, count);
        uint32_t needed = start + count;
        while (queue->elements.size() < needed) {
          queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
        }
        for (uint32_t i = 0; i < count; ++i) {
          std::string name =
              std::string(elem->text) + "__q__" + std::to_string(start + i);
          elems.push_back({elem, queue->elem_width, std::move(name)});
          total_width += queue->elem_width;
        }
        continue;
      }
    }

    if (has_dynamic && !elem->with_expr &&
        elem->kind == ExprKind::kIdentifier) {
      auto* queue = ctx.FindQueue(elem->text);
      if (queue) {
        if (!first_dynamic_consumed) {
          first_dynamic_consumed = true;
          uint32_t remaining =
              (rhs_width > fixed_sum) ? rhs_width - fixed_sum : 0;
          uint32_t count =
              queue->elem_width > 0 ? remaining / queue->elem_width : 0;
          queue->elements.clear();
          for (uint32_t i = 0; i < count; ++i) {
            queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
          }
          for (uint32_t i = 0; i < count; ++i) {
            std::string name =
                std::string(elem->text) + "__q__" + std::to_string(i);
            elems.push_back({elem, queue->elem_width, std::move(name)});
            total_width += queue->elem_width;
          }
        } else {
          queue->elements.clear();
        }
        continue;
      }
    }
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    elems.push_back({elem, var->value.width, {}});
    total_width += var->value.width;
  }
  return total_width;
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
    for (uint32_t b = 0; b < bits_to_copy; ++b) {
      uint32_t sbit = src_start + b;
      uint32_t dbit = dst_start + b;
      if (dbit >= total_width) break;
      uint32_t sw = sbit / 64, sb = sbit % 64;
      uint32_t dw = dbit / 64, db = dbit % 64;
      if (sw < stream.nwords) {
        if ((stream.words[sw].aval >> sb) & 1)
          reordered.words[dw].aval |= uint64_t{1} << db;
        if ((stream.words[sw].bval >> sb) & 1)
          reordered.words[dw].bval |= uint64_t{1} << db;
      }
    }
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
    uint32_t sw = sbit / 64, sb = sbit % 64;
    uint32_t dw = b / 64, db = b % 64;
    if (sw < stream.nwords) {
      if ((stream.words[sw].aval >> sb) & 1)
        result.words[dw].aval |= uint64_t{1} << db;
      if ((stream.words[sw].bval >> sb) & 1)
        result.words[dw].bval |= uint64_t{1} << db;
    }
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

// Forward unpack for the right-shift form: walk elements in stream order and
// write each target before resolving the next element's with-range, consuming
// bits from the most-significant end of the stream as we go. This makes an
// earlier-unpacked field visible to a later array's with-range (§11.4.14.4).
static void UnpackStreamingConcatLhsForward(const Expr* lhs,
                                            const Logic4Vec& rhs_val,
                                            SimContext& ctx, Arena& arena) {
  uint32_t total = rhs_val.width;
  uint32_t cursor = 0;  // bits already consumed from the MSB end
  auto take = [&](uint32_t w) -> Logic4Vec {
    if (cursor + w <= total)
      return ExtractStreamBits(rhs_val, total - cursor - w, w, total, arena);
    return MakeLogic4Vec(arena, w);
  };
  for (auto* elem : lhs->elements) {
    if (elem->with_expr && elem->kind == ExprKind::kIdentifier) {
      if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
        uint32_t start = 0, count = 0;
        bool in_range = ResolveWithRange(elem->with_expr, ctx, arena,
                                         ainfo->size, ainfo->lo, start, count);
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
        continue;
      }
      if (auto* queue = ctx.FindQueue(elem->text)) {
        uint32_t start = 0, count = 0;
        ResolveWithRange(elem->with_expr, ctx, arena,
                         static_cast<uint32_t>(queue->elements.size()), 0,
                         start, count);
        uint32_t needed = start + count;
        while (queue->elements.size() < needed)
          queue->elements.push_back(MakeLogic4Vec(arena, queue->elem_width));
        for (uint32_t i = 0; i < count; ++i) {
          Logic4Vec v = take(queue->elem_width);
          if (start + i < queue->elements.size())
            queue->elements[start + i] = v;
          cursor += queue->elem_width;
        }
        continue;
      }
    }
    auto* var = ResolveLhsVariable(elem, ctx);
    if (!var) continue;
    uint32_t w = var->value.width;
    var->value = take(w);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
    cursor += w;
  }
  if (cursor > total)
    ctx.GetDiag().Error({}, "too few bits in stream for streaming unpack");
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

  Logic4Vec stream;
  if (rhs_val.width > total_width) {
    uint32_t shift = rhs_val.width - total_width;
    stream = MakeLogic4Vec(arena, total_width);
    for (uint32_t b = 0; b < total_width; ++b) {
      uint32_t sbit = shift + b;
      uint32_t sw = sbit / 64, sb = sbit % 64;
      uint32_t dw = b / 64, db = b % 64;
      if (sw < rhs_val.nwords) {
        if ((rhs_val.words[sw].aval >> sb) & 1)
          stream.words[dw].aval |= uint64_t{1} << db;
        if ((rhs_val.words[sw].bval >> sb) & 1)
          stream.words[dw].bval |= uint64_t{1} << db;
      }
    }
  } else {
    stream = rhs_val;
  }

  if (lhs->op == TokenKind::kLtLt) {
    uint32_t ss = StreamSliceSizeForUnpack(lhs->lhs, ctx, arena);
    stream = ReverseStreamSlices(stream, total_width, ss, arena);
  }

  uint32_t bit_offset = total_width;
  for (auto& ei : elems) {
    bit_offset -= ei.width;
    if (!ei.target_name.empty()) {
      auto qpos = ei.target_name.find("__q__");
      if (qpos != std::string::npos) {
        auto qname = std::string_view(ei.target_name).substr(0, qpos);
        auto idx_str = ei.target_name.substr(qpos + 5);
        uint32_t idx = static_cast<uint32_t>(std::stoul(idx_str));
        auto* queue = ctx.FindQueue(qname);
        if (queue && idx < queue->elements.size()) {
          queue->elements[idx] = ExtractStreamBits(stream, bit_offset, ei.width,
                                                   total_width, arena);
        }
      } else {
        auto* var = ctx.FindVariable(ei.target_name);
        if (!var) {
          var = ctx.CreateVariable(*arena.Create<std::string>(ei.target_name),
                                   ei.width);
        }
        var->value =
            ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
        if (!var->is_4state) CoerceTo2State(var->value);
        var->NotifyWatchers();
      }
    } else {
      auto* var = ResolveLhsVariable(ei.expr, ctx);
      if (!var) continue;
      var->value =
          ExtractStreamBits(stream, bit_offset, ei.width, total_width, arena);
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
    }
  }
}

}  // namespace delta
