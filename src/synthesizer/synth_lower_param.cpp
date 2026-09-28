#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static uint32_t ConstBit(bool value) {
  return value ? AigGraph::kConstTrue : AigGraph::kConstFalse;
}

// Bit `bit` of the value `param` resolved to. RtlirParamDecl::resolved_value
// holds bits 63 down to 0, and resolved_high_words the words above them of a
// parameter declared wider, empty where none of those bits is set.
static bool ParamValueBit(const RtlirParamDecl& param, uint32_t bit) {
  constexpr uint32_t kWordBits = 64;
  if (bit < kWordBits) {
    return ((static_cast<uint64_t>(param.resolved_value) >> bit) & 1u) != 0;
  }
  uint32_t word = (bit - kWordBits) / kWordBits;
  if (word >= param.resolved_high_words.size()) return false;
  return ((param.resolved_high_words[word] >> ((bit - kWordBits) % kWordBits)) &
          1u) != 0;
}

// §11.5.1 puts a parameter among the operands a select addresses, and resolves
// the select against the declaration, so a parameter declared with a range is
// addressed over that range and any other over [width-1:0]. A range that does
// not span the width is the outermost of several packed dimensions, whose
// indices name elements rather than bits (§7.4.1), and falls back to
// [width-1:0] as SignalDeclaredRange falls back for a declared signal.
static PackedRange ParamDeclaredRange(const RtlirParamDecl& param,
                                      uint32_t width) {
  if (!param.has_decl_range_bounds) return PackedRange::Implicit(width);
  PackedRange range{param.decl_range_left, param.decl_range_right};
  if (range.HighIndex() - range.LowIndex() + 1 != static_cast<int64_t>(width)) {
    return PackedRange::Implicit(width);
  }
  return range;
}

// The address range of the unpacked dimension `dim` a parameter array was
// declared with, `[lo:hi]` or `[size]`, where its bounds fold. §7.4.2 makes
// `[size]` the range `[0:size-1]`.
static std::optional<RtlirUnpackedDim> FoldParamUnpackedDim(
    const Expr* dim, const ScopeMap& scope) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs, scope);
    auto right = ConstEvalInt(dim->rhs, scope);
    if (!left || !right) return std::nullopt;
    return RtlirUnpackedDim{*left, *right};
  }
  auto size = ConstEvalInt(dim, scope);
  if (!size || *size <= 0) return std::nullopt;
  return RtlirUnpackedDim{0, *size - 1};
}

void SynthLower::RecordParamSignal(const RtlirParamDecl& param,
                                   ParamStorageShape shape,
                                   std::vector<uint32_t> bits) {
  signal_widths_[param.name] = static_cast<uint32_t>(bits.size());
  signal_signed_[param.name] = shape.is_signed;
  signal_ranges_[param.name] = ParamDeclaredRange(param, shape.width);
  signal_bits_[param.name] = std::move(bits);
}

// The constant bits of an array of `width`-bit elements over the address
// range `dim`, from the positional pattern `pattern`, or empty where an
// element does not fold. The first element goes to the address at the left
// bound, as §10.9.1 assigns a positional pattern to an unpacked array.
static std::vector<uint32_t> ParamArrayBits(const Expr* pattern,
                                            RtlirUnpackedDim dim,
                                            uint32_t width,
                                            const ScopeMap& scope) {
  std::vector<uint32_t> bits(static_cast<size_t>(width) * dim.Size());
  for (uint32_t k = 0; k < dim.Size(); ++k) {
    auto element = ConstEvalInt(pattern->elements[k], scope);
    if (!element) return {};
    int64_t address = dim.left <= dim.right ? dim.left + k : dim.left - k;
    auto base = static_cast<uint32_t>(address - dim.Low()) * width;
    for (uint32_t b = 0; b < width; ++b) {
      bits[base + b] =
          ConstBit(((static_cast<uint64_t>(*element) >> b) & 1u) != 0);
    }
  }
  return bits;
}

bool SynthLower::MapParamArray(const RtlirParamDecl& param,
                               ParamStorageShape shape) {
  // The elaborator's own fold of an element select reads the same positional
  // pattern (ParamArrayElement in src/elaborator/const_eval.cpp). A resolved
  // value holds one integer, so each element is folded here from the pattern.
  if (param.unpacked_dims->size() != 1 || shape.width > 64) return false;
  auto dim = FoldParamUnpackedDim(param.unpacked_dims->front(), param_scope_);
  const Expr* value = param.override_expr != nullptr ? param.override_expr
                                                     : param.default_value;
  if (!dim || value == nullptr || value->kind != ExprKind::kAssignmentPattern ||
      !value->pattern_keys.empty() || value->elements.size() != dim->Size()) {
    return false;
  }
  std::vector<uint32_t> bits =
      ParamArrayBits(value, *dim, shape.width, param_scope_);
  if (bits.empty()) return false;
  RecordArrayShape(param.name, shape.width, 1, {*dim});
  unpacked_arrays_.insert(param.name);
  RecordParamSignal(param, shape, std::move(bits));
  return true;
}

bool SynthLower::MapParam(const RtlirParamDecl& param) {
  // A real or a string parameter holds its value outside
  // RtlirParamDecl::resolved_value, and a parameter declared in a generate
  // block names a different value in each block (§23.9) where the signal
  // tables hold one per name.
  if (param.is_real_value || param.decl_is_real || param.is_string_value ||
      !param.gen_block_prefix.empty()) {
    return false;
  }
  ParamStorageShape shape = ParamStorageShapeOf(param);
  if (param.unpacked_dims != nullptr) return MapParamArray(param, shape);
  if (!param.is_resolved) return false;
  std::vector<uint32_t> bits(shape.width);
  for (uint32_t b = 0; b < shape.width; ++b) {
    bits[b] = ConstBit(ParamValueBit(param, b));
  }
  RecordParamSignal(param, shape, std::move(bits));
  return true;
}

void SynthLower::MapParams(const RtlirModule* mod) {
  for (const auto& param : mod->params) {
    // A type parameter names a type rather than a value, so no operand reads
    // it.
    if (param.is_type_param || signal_widths_.count(param.name) != 0) continue;
    if (!MapParam(param)) unlowered_params_.insert(param.name);
  }
}

bool SynthLower::ReportIfUnloweredParam(const Expr* expr, const Expr* name) {
  if (name == nullptr || name->kind != ExprKind::kIdentifier ||
      unlowered_params_.count(name->text) == 0 ||
      signal_widths_.count(name->text) != 0) {
    return false;
  }
  ReportExprUnlowered(expr,
                      "parameter's value has no lowering in the synthesizer",
                      Subclause("6.20"));
  return true;
}

}  // namespace delta
