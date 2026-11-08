#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static constexpr uint32_t kSelectIndexBits = 32;

PackedRange SynthLower::BaseRange(const Expr* base) {
  if (!base || base->kind != ExprKind::kIdentifier) {
    return PackedRange::Implicit(0);
  }
  auto it = signal_ranges_.find(base->text);
  if (it != signal_ranges_.end()) return it->second;
  return PackedRange::Implicit(SignalWidth(base->text));
}

bool SynthLower::IsVectorSelect(const Expr* sel) {
  if (!sel || !sel->base || sel->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  return unpacked_arrays_.count(sel->base->text) == 0;
}

static const Expr* SelectRootName(const Expr* expr) {
  while (expr && expr->kind == ExprKind::kSelect) expr = expr->base;
  return expr;
}

bool SynthLower::RecordArrayShape(std::string_view name, uint32_t elem_width,
                                  uint32_t num_dims,
                                  const std::vector<RtlirUnpackedDim>& dims) {
  if (num_dims == 0 || dims.size() != num_dims) return false;
  ArrayShape shape;
  shape.elem_width = elem_width;
  shape.dims.reserve(dims.size());
  for (const auto& dim : dims) {
    shape.dims.push_back(ArrayDim{dim.Low(), dim.Size()});
  }
  array_shapes_[name] = std::move(shape);
  return true;
}

uint32_t SynthLower::ArrayStorageWidth(std::string_view name,
                                       uint32_t elem_width) {
  auto it = array_shapes_.find(name);
  if (it == array_shapes_.end()) return elem_width;
  return elem_width * it->second.Count();
}

const SynthLower::ArrayShape* SynthLower::ArrayShapeOf(const Expr* base) {
  if (!base || base->kind != ExprKind::kIdentifier) return nullptr;
  auto it = array_shapes_.find(base->text);
  return it == array_shapes_.end() ? nullptr : &it->second;
}

static std::vector<const Expr*> CollectSelectChain(const Expr* sel,
                                                   const Expr** name) {
  std::vector<const Expr*> nodes;
  const Expr* e = sel;
  for (; e != nullptr && e->kind == ExprKind::kSelect; e = e->base) {
    nodes.push_back(e);
  }
  *name = e;
  std::reverse(nodes.begin(), nodes.end());
  return nodes;
}

SynthLower::SelectStorage SynthLower::ResolveArraySelect(const Expr* sel) {
  const Expr* name = nullptr;
  std::vector<const Expr*> nodes = CollectSelectChain(sel, &name);
  const ArrayShape* shape = ArrayShapeOf(name);
  if (shape == nullptr || nodes.size() != shape->dims.size()) return {};

  int64_t element = 0;
  bool out_of_bounds = false;
  for (size_t d = 0; d < shape->dims.size(); ++d) {
    if (nodes[d]->index_end) return {};
    std::optional<int64_t> address = ConstEvalInt(nodes[d]->index, scope_);
    if (!address) return {};
    int64_t offset = *address - shape->dims[d].lo;
    if (offset < 0 || offset >= static_cast<int64_t>(shape->dims[d].count)) {
      out_of_bounds = true;
    }
    element = element * static_cast<int64_t>(shape->dims[d].count) + offset;
  }
  if (out_of_bounds) element = shape->Count();
  return {name->text, element * static_cast<int64_t>(shape->elem_width),
          shape->elem_width};
}

SynthLower::ArraySelectKind SynthLower::ClassifyArraySelect(const Expr* sel) {
  const Expr* name = nullptr;
  std::vector<const Expr*> nodes = CollectSelectChain(sel, &name);
  const ArrayShape* shape = ArrayShapeOf(name);
  if (shape == nullptr) return ArraySelectKind::kNotArray;
  if (nodes.size() < shape->dims.size()) return ArraySelectKind::kSlice;
  if (nodes.size() == shape->dims.size()) return ArraySelectKind::kElement;
  return ArraySelectKind::kInsideElement;
}

SynthLower::SelectStorage SynthLower::ResolveSelect(const Expr* sel) {
  if (!sel || !sel->base) return {};

  switch (ClassifyArraySelect(sel)) {
    case ArraySelectKind::kSlice:
      return {};
    case ArraySelectKind::kElement:
      return ResolveArraySelect(sel);
    default:
      break;
  }

  SelectStorage base_run;
  if (sel->base->kind == ExprKind::kSelect) {
    base_run = ResolveSelect(sel->base);
    if (base_run.count == 0) return {};
  } else {
    if (!IsVectorSelect(sel)) return {};
    base_run = {sel->base->text, 0, SignalWidth(sel->base->text)};
  }

  std::optional<int64_t> index = ConstEvalInt(sel->index, scope_);
  if (!index) return {};

  int64_t first = *index;
  int64_t second = *index;
  if (sel->index_end) {
    std::optional<int64_t> end = ConstEvalInt(sel->index_end, scope_);
    if (!end) return {};
    PartSelectIndices indices = PartSelectTargetIndices(
        *index, *end, sel->is_part_select_plus, sel->is_part_select_minus);
    first = indices.first;
    second = indices.second;
  }

  PackedRange range = BaseRange(SelectRootName(sel->base));
  int64_t first_offset = range.OffsetOf(first);
  int64_t second_offset = range.OffsetOf(second);
  int64_t lo = std::min(first_offset, second_offset);
  int64_t hi = std::max(first_offset, second_offset);
  return {base_run.name, base_run.lo + lo, static_cast<uint32_t>(hi - lo + 1)};
}

uint32_t SynthLower::LowerArraySelectBit(const Expr* expr, AigGraph& aig,
                                         uint32_t bit) {
  const ArrayShape* shape = ArrayShapeOf(expr->base);
  if (shape != nullptr && shape->dims.size() != 1) shape = nullptr;
  if (!shape || expr->index_end) {
    ReportExprUnlowered(expr,
                        "an element of this unpacked array has no lowering in "
                        "the synthesizer",
                        Subclause("11.5.2"));
    return AigGraph::kConstFalse;
  }
  if (bit >= shape->elem_width) return AigGraph::kConstFalse;

  uint32_t result = AigGraph::kConstFalse;
  for (uint32_t element = 0; element < shape->dims[0].count; ++element) {
    uint32_t source =
        GetSignalBit(expr->base->text, element * shape->elem_width + bit);
    result = aig.AddMux(
        ExprEqualsValue(expr->index, aig, shape->dims[0].lo + element), source,
        result);
  }
  return result;
}

bool SynthLower::LowerArrayTarget(const Expr* lhs, const Expr* rhs,
                                  AigGraph& aig) {
  const ArrayShape* shape = ArrayShapeOf(lhs->base);
  if (shape != nullptr && shape->dims.size() != 1) shape = nullptr;
  if (!shape || lhs->index_end) return false;

  propagated_width_ = shape->elem_width;
  propagated_signed_ = IsSignedExpr(rhs);
  for (uint32_t element = 0; element < shape->dims[0].count; ++element) {
    uint32_t selected =
        ExprEqualsValue(lhs->index, aig, shape->dims[0].lo + element);
    for (uint32_t b = 0; b < shape->elem_width; ++b) {
      uint32_t offset = element * shape->elem_width + b;
      uint32_t held = GetSignalBit(lhs->base->text, offset);
      uint32_t driven = LowerAssignRhsBit(rhs, aig, b);
      SetSignalBit(lhs->base->text, offset, aig.AddMux(selected, driven, held));
    }
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
  return true;
}

uint32_t SynthLower::ExprEqualsValue(const Expr* expr, AigGraph& aig,
                                     int64_t value) {
  uint32_t match = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < kSelectIndexBits; ++b) {
    uint32_t want = ((static_cast<uint64_t>(value) >> b) & 1u) != 0
                        ? AigGraph::kConstTrue
                        : AigGraph::kConstFalse;
    uint32_t have = LowerExprBit(expr, aig, b);
    match = aig.AddAnd(match, aig.AddNot(aig.AddXor(have, want)));
  }
  return match;
}

int64_t SynthLower::VariableSelectWidth(const Expr* expr) {
  if (!expr->index_end) return 1;
  if (!expr->is_part_select_plus && !expr->is_part_select_minus) return 0;
  std::optional<int64_t> end = ConstEvalInt(expr->index_end, scope_);
  if (!end || *end <= 0) return 0;
  return *end;
}

int64_t SynthLower::VariableSelectIndex(const Expr* expr, int64_t value,
                                        int64_t width, uint32_t bit) {
  return PartSelectTargetIndices(value, width, expr->is_part_select_plus,
                                 expr->is_part_select_minus)
             .first +
         static_cast<int64_t>(bit);
}

static bool IsExpressionSelectOperand(const Expr* base) {
  if (base == nullptr) return false;
  switch (base->kind) {
    case ExprKind::kBinary:
    case ExprKind::kUnary:
    case ExprKind::kTernary:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
    case ExprKind::kSelect:
      return true;
    default:
      return false;
  }
}

uint32_t SynthLower::LowerVariableSelectBit(const Expr* expr, AigGraph& aig,
                                            uint32_t bit) {
  if (!IsVectorSelect(expr)) {
    if (expr->base && expr->base->kind == ExprKind::kIdentifier &&
        unpacked_arrays_.count(expr->base->text) != 0) {
      return LowerArraySelectBit(expr, aig, bit);
    }
    if (IsExpressionSelectOperand(expr->base)) {
      return LowerExprSelectBit(expr, aig, bit);
    }
    return AigGraph::kConstFalse;
  }
  int64_t width = VariableSelectWidth(expr);
  if (width == 0 || static_cast<int64_t>(bit) >= width) {
    return AigGraph::kConstFalse;
  }

  PackedRange range = BaseRange(expr->base);
  uint32_t base_width = SignalWidth(expr->base->text);
  int64_t high = std::max(range.left, range.right);
  uint32_t result = AigGraph::kConstFalse;
  for (int64_t value = 0; value <= high + width - 1; ++value) {
    int64_t offset =
        range.OffsetOf(VariableSelectIndex(expr, value, width, bit));
    if (offset < 0 || offset >= static_cast<int64_t>(base_width)) continue;
    uint32_t source =
        GetSignalBit(expr->base->text, static_cast<uint32_t>(offset));
    result =
        aig.AddMux(ExprEqualsValue(expr->index, aig, value), source, result);
  }
  return result;
}

uint32_t SynthLower::LowerSelectBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  if (ReportIfUnloweredParam(expr, SelectRootName(expr))) {
    return AigGraph::kConstFalse;
  }
  SelectStorage storage = ResolveSelect(expr);
  if (storage.count == 0) return LowerVariableSelectBit(expr, aig, bit);
  if (bit >= storage.count) return AigGraph::kConstFalse;

  int64_t offset = storage.lo + bit;
  if (offset < 0) return AigGraph::kConstFalse;
  return GetSignalBit(storage.name, static_cast<uint32_t>(offset));
}

uint32_t SynthLower::LowerExprSelectBit(const Expr* expr, AigGraph& aig,
                                        uint32_t bit) {
  std::optional<int64_t> index = ConstEvalInt(expr->index, scope_);
  if (!index) return AigGraph::kConstFalse;
  int64_t first = *index;
  int64_t second = *index;
  if (expr->index_end != nullptr) {
    std::optional<int64_t> end = ConstEvalInt(expr->index_end, scope_);
    if (!end) return AigGraph::kConstFalse;
    PartSelectIndices indices = PartSelectTargetIndices(
        *index, *end, expr->is_part_select_plus, expr->is_part_select_minus);
    first = indices.first;
    second = indices.second;
  }
  int64_t lo = std::min(first, second);
  int64_t hi = std::max(first, second);
  int64_t offset = lo + static_cast<int64_t>(bit);
  if (offset < 0 || offset > hi) return AigGraph::kConstFalse;
  return LowerExprBit(expr->base, aig, static_cast<uint32_t>(offset));
}

void SynthLower::LowerSelectTarget(const Expr* lhs, const Expr* rhs,
                                   AigGraph& aig) {
  SelectStorage storage = ResolveSelect(lhs);
  if (storage.count == 0) {
    if (LowerArrayTarget(lhs, rhs, aig)) return;
    ReportUnloweredTarget(lhs);
    return;
  }

  propagated_width_ = storage.count;
  propagated_signed_ = IsSignedExpr(rhs);
  for (uint32_t b = 0; b < storage.count; ++b) {
    int64_t offset = storage.lo + static_cast<int64_t>(b);
    if (offset < 0) continue;
    SetSignalBit(storage.name, static_cast<uint32_t>(offset),
                 LowerAssignRhsBit(rhs, aig, b));
  }
  propagated_width_ = 0;
  propagated_signed_ = false;
}

}  // namespace delta
