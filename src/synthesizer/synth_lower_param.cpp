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
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static uint32_t ConstBit(bool value) {
  return value ? AigGraph::kConstTrue : AigGraph::kConstFalse;
}

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

static PackedRange ParamDeclaredRange(const RtlirParamDecl& param,
                                      uint32_t width) {
  if (!param.has_decl_range_bounds) return PackedRange::Implicit(width);
  PackedRange range{param.decl_range_left, param.decl_range_right};
  if (range.HighIndex() - range.LowIndex() + 1 != static_cast<int64_t>(width)) {
    return PackedRange::Implicit(width);
  }
  return range;
}

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

static std::vector<uint32_t> ParamBits(const RtlirParamDecl& param,
                                       uint32_t width) {
  std::vector<uint32_t> bits(width);
  for (uint32_t b = 0; b < width; ++b) {
    bits[b] = ConstBit(ParamValueBit(param, b));
  }
  return bits;
}

bool SynthLower::MapParam(const RtlirParamDecl& param) {
  if (param.is_real_value || param.decl_is_real || param.is_string_value ||
      !param.gen_block_prefix.empty()) {
    return false;
  }
  ParamStorageShape shape = ParamStorageShapeOf(param);
  if (param.unpacked_dims != nullptr) return MapParamArray(param, shape);
  if (!param.is_resolved) return false;
  RecordParamSignal(param, shape, ParamBits(param, shape.width));
  return true;
}

bool SynthLower::RecordBlockParam(const RtlirParamDecl& param) {
  if (param.gen_block_prefix.empty() || !param.is_resolved ||
      param.is_real_value || param.decl_is_real || param.is_string_value ||
      param.unpacked_dims != nullptr) {
    return false;
  }
  block_params_.push_back(&param);
  return true;
}

void SynthLower::MapParams(const RtlirModule* mod) {
  for (const auto& param : mod->params) {
    if (param.is_type_param || RecordBlockParam(param) ||
        signal_widths_.count(param.name) != 0) {
      continue;
    }
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

void SynthLower::InstallScopeConstant(std::string_view name,
                                      std::vector<uint32_t> bits,
                                      bool is_signed, PackedRange range) {
  bool kept = std::any_of(
      shadowed_signals_.begin(), shadowed_signals_.end(),
      [name](const ShadowedSignal& held) { return held.name == name; });
  auto it = signal_bits_.find(name);
  if (!kept) {
    ShadowedSignal held;
    held.name = name;
    if (it != signal_bits_.end()) {
      held.recorded = true;
      held.is_unpacked = unpacked_arrays_.count(name) != 0;
      held.width = signal_widths_[name];
      held.is_signed = signal_signed_[name];
      held.range = signal_ranges_[name];
      held.bits = it->second;
    }
    shadowed_signals_.push_back(std::move(held));
  }
  unpacked_arrays_.erase(name);
  signal_widths_[name] = static_cast<uint32_t>(bits.size());
  signal_signed_[name] = is_signed;
  signal_ranges_[name] = range;
  signal_bits_[name] = std::move(bits);
}

void SynthLower::RestoreShadowedSignals() {
  for (ShadowedSignal& held : shadowed_signals_) {
    if (!held.recorded) {
      signal_bits_.erase(held.name);
      signal_widths_.erase(held.name);
      signal_signed_.erase(held.name);
      signal_ranges_.erase(held.name);
      continue;
    }
    if (held.is_unpacked) unpacked_arrays_.insert(held.name);
    signal_widths_[held.name] = held.width;
    signal_signed_[held.name] = held.is_signed;
    signal_ranges_[held.name] = held.range;
    signal_bits_[held.name] = std::move(held.bits);
  }
  shadowed_signals_.clear();
}

static constexpr uint32_t kIntegerBits = 32;

static std::vector<uint32_t> IntegerBits(int64_t value) {
  std::vector<uint32_t> bits(kIntegerBits);
  for (uint32_t b = 0; b < kIntegerBits; ++b) {
    bits[b] = ConstBit(((static_cast<uint64_t>(value) >> b) & 1u) != 0);
  }
  return bits;
}

void SynthLower::SetGenScope(const GenBlockConsts& consts,
                             const GenBlockPrefixes& prefixes) {
  RestoreShadowedSignals();
  scope_ = param_scope_;
  gen_prefix_ = prefixes.empty() ? std::string_view{} : prefixes.back();
  for (const auto& [name, value] : consts) {
    scope_[name] = value;
    InstallScopeConstant(name, IntegerBits(value), true,
                         PackedRange::Implicit(kIntegerBits));
  }
  for (std::string_view prefix : prefixes) {
    for (const RtlirParamDecl* param : block_params_) {
      if (param->gen_block_prefix != prefix) continue;
      scope_[param->name] = param->resolved_value;
      ParamStorageShape shape = ParamStorageShapeOf(*param);
      InstallScopeConstant(param->name, ParamBits(*param, shape.width),
                           shape.is_signed,
                           ParamDeclaredRange(*param, shape.width));
    }
  }
}

}  // namespace delta
