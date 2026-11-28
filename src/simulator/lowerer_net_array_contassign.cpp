#include "simulator/lowerer_net_array_contassign.h"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <optional>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

struct DimSpan {
  int64_t left = 0;
  int64_t right = 0;

  [[nodiscard]] size_t Count() const {
    return static_cast<size_t>(std::llabs(right - left)) + 1;
  }
};

struct ArrayRef {
  Expr* root = nullptr;
  uint32_t elem_width = 0;
  std::vector<DimSpan> spans;
  std::vector<bool> fixed;
};

std::vector<DimSpan> DeclaredSpans(const ArrayInfo& info) {
  std::vector<DimSpan> spans;
  auto add = [&spans](int64_t lo, uint32_t size, bool descending) {
    const int64_t kHigh = lo + static_cast<int64_t>(size) - 1;
    spans.push_back(descending ? DimSpan{kHigh, lo} : DimSpan{lo, kHigh});
  };
  if (info.dim_sizes.empty()) {
    add(info.lo, info.size, info.is_descending);
    return spans;
  }
  for (size_t d = 0; d < info.dim_sizes.size(); ++d) {
    add(info.dim_los[d], info.dim_sizes[d],
        d < info.dim_descending.size() && info.dim_descending[d]);
  }
  return spans;
}

bool KnownIndex(const Expr* e, SimContext& ctx, int64_t& out) {
  Logic4Vec value = EvalExpr(e, ctx, ctx.GetArena());
  if (!value.IsKnown()) return false;
  out = static_cast<int64_t>(value.ToUint64());
  return true;
}

bool NarrowSpan(const Expr* select, bool last, SimContext& ctx, DimSpan& span) {
  if (select->is_part_select_plus || select->is_part_select_minus) return false;
  int64_t first = 0;
  if (!KnownIndex(select->index, ctx, first)) return false;
  if (select->index_end == nullptr) {
    span = {first, first};
    return true;
  }
  int64_t second = 0;
  if (!last || !KnownIndex(select->index_end, ctx, second)) return false;
  span = {first, second};
  return true;
}

std::optional<ArrayRef> ResolveArrayRef(Expr* e, SimContext& ctx) {
  std::vector<const Expr*> chain;
  Expr* root = e;
  while (root->kind == ExprKind::kSelect && root->base != nullptr) {
    chain.push_back(root);
    root = root->base;
  }
  if (root->kind != ExprKind::kIdentifier) return std::nullopt;
  const ArrayInfo* info = ctx.FindArrayInfo(root->text);
  if (info == nullptr || info->is_dynamic || info->is_queue)
    return std::nullopt;
  ArrayRef ref{root, info->elem_width, DeclaredSpans(*info), {}};
  ref.fixed.assign(ref.spans.size(), false);
  if (chain.size() > ref.spans.size()) return std::nullopt;
  size_t depth = 0;
  for (auto it = chain.rbegin(); it != chain.rend(); ++it, ++depth) {
    if (!NarrowSpan(*it, std::next(it) == chain.rend(), ctx, ref.spans[depth]))
      return std::nullopt;
    ref.fixed[depth] = (*it)->index_end == nullptr;
  }
  return ref;
}

std::vector<std::vector<int64_t>> LeafAddresses(
    const std::vector<DimSpan>& spans) {
  std::vector<std::vector<int64_t>> leaves(1);
  for (const DimSpan& span : spans) {
    const int64_t kStep = span.left <= span.right ? 1 : -1;
    std::vector<std::vector<int64_t>> next;
    for (const std::vector<int64_t>& prefix : leaves) {
      for (size_t k = 0; k < span.Count(); ++k) {
        next.push_back(prefix);
        next.back().push_back(span.left + kStep * static_cast<int64_t>(k));
      }
    }
    leaves = std::move(next);
  }
  return leaves;
}

Expr* ElementAt(Expr* root, const std::vector<int64_t>& address, Arena& arena) {
  Expr* element = root;
  for (int64_t at : address) {
    auto* index = arena.Create<Expr>();
    index->kind = ExprKind::kIntegerLiteral;
    index->int_val = static_cast<uint64_t>(at);
    auto* select = arena.Create<Expr>();
    select->kind = ExprKind::kSelect;
    select->base = element;
    select->index = index;
    element = select;
  }
  return element;
}

bool FlattenPattern(Expr* e, const std::vector<DimSpan>& free, size_t depth,
                    std::vector<Expr*>& out) {
  if (depth == free.size()) {
    out.push_back(e);
    return true;
  }
  if (e->kind != ExprKind::kAssignmentPattern || !e->pattern_keys.empty() ||
      e->is_pattern_replication || e->elements.size() != free[depth].Count())
    return false;
  for (Expr* item : e->elements) {
    if (!FlattenPattern(item, free, depth + 1, out)) return false;
  }
  return true;
}

bool SourceLeaves(Expr* rhs, const std::vector<DimSpan>& free, SimContext& ctx,
                  Arena& arena, std::vector<Expr*>& out) {
  if (rhs->kind == ExprKind::kAssignmentPattern)
    return FlattenPattern(rhs, free, 0, out);
  std::optional<ArrayRef> source = ResolveArrayRef(rhs, ctx);
  if (!source) return false;
  for (const std::vector<int64_t>& address : LeafAddresses(source->spans))
    out.push_back(ElementAt(source->root, address, arena));
  return true;
}

}  // namespace

bool SplitNetArrayContAssign(const RtlirContAssign& ca, SimContext& ctx,
                             Arena& arena,
                             std::vector<RtlirContAssign>& pieces) {
  const Expr* root = ca.lhs;
  while (root->kind == ExprKind::kSelect && root->base != nullptr)
    root = root->base;
  if (root->kind != ExprKind::kIdentifier || ctx.FindNet(root->text) == nullptr)
    return false;
  std::optional<ArrayRef> target = ResolveArrayRef(ca.lhs, ctx);
  if (!target) return false;
  std::vector<DimSpan> free;
  for (size_t d = 0; d < target->spans.size(); ++d) {
    if (!target->fixed[d]) free.push_back(target->spans[d]);
  }
  if (free.empty()) return false;
  const std::vector<std::vector<int64_t>> kLeaves =
      LeafAddresses(target->spans);
  std::vector<Expr*> sources;
  if (!SourceLeaves(ca.rhs, free, ctx, arena, sources) ||
      sources.size() != kLeaves.size())
    return false;
  for (size_t k = 0; k < kLeaves.size(); ++k) {
    RtlirContAssign piece = ca;
    piece.lhs = ElementAt(target->root, kLeaves[k], arena);
    piece.rhs = sources[k];
    piece.width = target->elem_width;
    pieces.push_back(std::move(piece));
  }
  return true;
}

}  // namespace delta
