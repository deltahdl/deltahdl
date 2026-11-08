#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/assertion_walk.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static const TypedefMap* g_typedefs = nullptr;
static const std::unordered_set<std::string_view>* g_aggregate_typedef_names =
    nullptr;
static const TypeRefComparer* g_type_ref_compare = nullptr;

TypedefRegistryGuard::TypedefRegistryGuard(
    const TypedefMap* typedefs,
    const std::unordered_set<std::string_view>* aggregate_names,
    const TypeRefComparer* compare)
    : prev_(g_typedefs),
      prev_aggregate_names_(g_aggregate_typedef_names),
      prev_compare_(g_type_ref_compare) {
  g_typedefs = typedefs;
  g_aggregate_typedef_names = aggregate_names;
  g_type_ref_compare = compare;
}

TypedefRegistryGuard::~TypedefRegistryGuard() {
  g_typedefs = prev_;
  g_aggregate_typedef_names = prev_aggregate_names_;
  g_type_ref_compare = prev_compare_;
}

bool IsTypeRefComparison(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kBinary) return false;
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq &&
      expr->op != TokenKind::kEqEqEq && expr->op != TokenKind::kBangEqEq)
    return false;
  return expr->lhs != nullptr && expr->lhs->kind == ExprKind::kTypeRef &&
         expr->rhs != nullptr && expr->rhs->kind == ExprKind::kTypeRef;
}

std::optional<int64_t> RegisteredTypeRefCompare(const Expr* expr) {
  if (g_type_ref_compare == nullptr || !IsTypeRefComparison(expr))
    return std::nullopt;
  return (*g_type_ref_compare)(expr, RegisteredModule());
}

const DataType* RegisteredTypedef(std::string_view name) {
  if (g_typedefs == nullptr) return nullptr;
  if (g_aggregate_typedef_names != nullptr &&
      g_aggregate_typedef_names->count(name) != 0)
    return nullptr;
  auto it = g_typedefs->find(name);
  return it == g_typedefs->end() ? nullptr : &it->second;
}

const std::unordered_map<std::string_view, DataType>* RegisteredTypedefMap() {
  return g_typedefs;
}

uint32_t RegisteredTypeWidth(const DataType& type, const ScopeMap& scope) {
  return g_typedefs == nullptr ? EvalTypeWidth(type)
                               : EvalTypeWidth(type, *g_typedefs, scope);
}

static std::optional<int64_t> IntegralKeywordWidth(std::string_view kw) {
  if (kw == "bit" || kw == "logic" || kw == "reg") return 1;
  if (kw == "byte") return 8;
  if (kw == "shortint") return 16;
  if (kw == "int" || kw == "integer") return 32;
  if (kw == "longint" || kw == "time") return 64;
  return std::nullopt;
}

static std::optional<int64_t> RangedKeywordBits(const Expr* a,
                                                const ScopeMap& scope) {
  if (a->kind != ExprKind::kSelect || !a->index || !a->index_end ||
      a->is_part_select_plus || a->is_part_select_minus || !a->base ||
      a->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  auto atom = IntegralKeywordWidth(a->base->text);
  if (!atom) return std::nullopt;
  auto hi = ConstEvalInt(a->index, scope);
  auto lo = ConstEvalInt(a->index_end, scope);
  if (!hi || !lo) return std::nullopt;
  int64_t span = (*hi >= *lo ? *hi - *lo : *lo - *hi) + 1;
  return *atom * span;
}

static bool HasDeclaredWidth(const RtlirParamDecl& pd) {
  return pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
}

ParamStorageShape ParamStorageShapeOf(const RtlirParamDecl& param) {
  bool declared = HasDeclaredWidth(param);
  if (declared && param.decl_width > 0)
    return {param.decl_width, param.decl_is_signed};
  if (!declared && param.value_width > 0)
    return {param.value_width, param.value_is_signed || param.decl_is_signed};
  return {32, param.decl_is_signed};
}

static const Expr* LiteralOverrideExpr(const RtlirParamDecl& pd) {
  if (pd.override_expr == nullptr ||
      pd.override_expr->kind != ExprKind::kIntegerLiteral)
    return nullptr;
  return pd.override_expr;
}

static std::optional<int64_t> ParamDeclBits(const RtlirParamDecl& pd) {
  if (pd.is_type_param || pd.is_real_value || pd.is_string_value)
    return std::nullopt;
  if (HasDeclaredWidth(pd)) {
    if (pd.decl_width == 0) return std::nullopt;
    return static_cast<int64_t>(pd.decl_width);
  }
  if (pd.value_width != 0) return static_cast<int64_t>(pd.value_width);
  if (pd.from_override) {
    const Expr* lit = LiteralOverrideExpr(pd);
    if (lit == nullptr) return std::nullopt;
    return static_cast<int64_t>(ConstLiteralWidth(lit));
  }
  auto value = ConstEvalFull(pd.default_value, RegisteredModuleScope());
  if (!value) return std::nullopt;
  return static_cast<int64_t>(value->width);
}

static std::optional<int64_t> ArrayBits(uint32_t elem_bits, uint32_t num_dims,
                                        const std::vector<uint32_t>& sizes) {
  if (sizes.size() != num_dims) return std::nullopt;
  int64_t bits = elem_bits;
  for (uint32_t size : sizes) bits *= size;
  return bits;
}

static std::optional<int64_t> RegisteredVariableBits(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& var : mod->variables) {
    if (var.name != name) continue;
    if (var.is_real || var.is_string || var.is_event || var.is_chandle ||
        !var.class_type_name.empty())
      return std::nullopt;
    return ArrayBits(var.width, var.num_unpacked_dims, var.unpacked_dim_sizes);
  }
  return std::nullopt;
}

static std::optional<int64_t> RegisteredNetBits(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& net : mod->nets) {
    if (net.name != name) continue;
    return ArrayBits(net.width, net.num_unpacked_dims, net.unpacked_dim_sizes);
  }
  return std::nullopt;
}

static std::optional<int64_t> RegisteredTypedefBits(std::string_view name,
                                                    const ScopeMap& scope) {
  if (g_typedefs == nullptr) return std::nullopt;
  auto it = g_typedefs->find(name);
  if (it == g_typedefs->end()) return std::nullopt;
  if (g_aggregate_typedef_names != nullptr &&
      g_aggregate_typedef_names->count(name) != 0)
    return std::nullopt;
  uint32_t width = EvalTypeWidth(it->second, *g_typedefs, scope);
  if (width == 0) return std::nullopt;
  return static_cast<int64_t>(width);
}

static std::optional<int64_t> IdentifierBits(const Expr* a,
                                             const ScopeMap& scope) {
  if (auto w = IntegralKeywordWidth(a->text)) return w;
  if (auto w = RegisteredTypedefBits(a->text, scope)) return w;
  if (const RtlirParamDecl* pd = RegisteredParamNamed(a->text))
    return ParamDeclBits(*pd);
  if (auto w = RegisteredVariableBits(a->text)) return w;
  return RegisteredNetBits(a->text);
}

static std::optional<int64_t> SelfDeterminedBits(const Expr* a,
                                                 const ScopeMap& scope);

enum class BitLengthRule : std::uint8_t {
  kMaxOfOperands,
  kLeftOperand,
  kOneBit
};

static std::optional<BitLengthRule> BitLengthRuleOf(const Expr* a) {
  static const std::unordered_map<TokenKind, BitLengthRule> kBinary{
      {TokenKind::kPlus, BitLengthRule::kMaxOfOperands},
      {TokenKind::kMinus, BitLengthRule::kMaxOfOperands},
      {TokenKind::kStar, BitLengthRule::kMaxOfOperands},
      {TokenKind::kSlash, BitLengthRule::kMaxOfOperands},
      {TokenKind::kPercent, BitLengthRule::kMaxOfOperands},
      {TokenKind::kAmp, BitLengthRule::kMaxOfOperands},
      {TokenKind::kPipe, BitLengthRule::kMaxOfOperands},
      {TokenKind::kCaret, BitLengthRule::kMaxOfOperands},
      {TokenKind::kTildeCaret, BitLengthRule::kMaxOfOperands},
      {TokenKind::kCaretTilde, BitLengthRule::kMaxOfOperands},
      {TokenKind::kLt, BitLengthRule::kOneBit},
      {TokenKind::kGt, BitLengthRule::kOneBit},
      {TokenKind::kLtEq, BitLengthRule::kOneBit},
      {TokenKind::kGtEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEq, BitLengthRule::kOneBit},
      {TokenKind::kBangEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEqEq, BitLengthRule::kOneBit},
      {TokenKind::kBangEqEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEqQuestion, BitLengthRule::kOneBit},
      {TokenKind::kBangEqQuestion, BitLengthRule::kOneBit},
      {TokenKind::kAmpAmp, BitLengthRule::kOneBit},
      {TokenKind::kPipePipe, BitLengthRule::kOneBit},
      {TokenKind::kArrow, BitLengthRule::kOneBit},
      {TokenKind::kLtDashGt, BitLengthRule::kOneBit},
  };
  static const std::unordered_map<TokenKind, BitLengthRule> kUnary{
      {TokenKind::kPlus, BitLengthRule::kLeftOperand},
      {TokenKind::kMinus, BitLengthRule::kLeftOperand},
      {TokenKind::kTilde, BitLengthRule::kLeftOperand},
      {TokenKind::kAmp, BitLengthRule::kOneBit},
      {TokenKind::kTildeAmp, BitLengthRule::kOneBit},
      {TokenKind::kPipe, BitLengthRule::kOneBit},
      {TokenKind::kTildePipe, BitLengthRule::kOneBit},
      {TokenKind::kCaret, BitLengthRule::kOneBit},
      {TokenKind::kTildeCaret, BitLengthRule::kOneBit},
      {TokenKind::kCaretTilde, BitLengthRule::kOneBit},
      {TokenKind::kBang, BitLengthRule::kOneBit},
  };
  if (a->kind == ExprKind::kBinary && SizedByLeftOperand(a->op))
    return BitLengthRule::kLeftOperand;
  const auto& rules = a->kind == ExprKind::kUnary ? kUnary : kBinary;
  auto it = rules.find(a->op);
  if (it == rules.end()) return std::nullopt;
  return it->second;
}

static std::optional<int64_t> OperatorBits(const Expr* a,
                                           const ScopeMap& scope) {
  auto rule = BitLengthRuleOf(a);
  if (!rule) return std::nullopt;
  if (*rule == BitLengthRule::kOneBit) return 1;
  auto l = SelfDeterminedBits(a->lhs, scope);
  if (*rule == BitLengthRule::kLeftOperand) return l;
  auto r = SelfDeterminedBits(a->rhs, scope);
  if (!l || !r) return std::nullopt;
  return std::max(*l, *r);
}

static std::optional<int64_t> TernaryBits(const Expr* a,
                                          const ScopeMap& scope) {
  auto t = SelfDeterminedBits(a->true_expr, scope);
  auto f = SelfDeterminedBits(a->false_expr, scope);
  if (!t || !f) return std::nullopt;
  return std::max(*t, *f);
}

static std::optional<int64_t> SelfDeterminedBits(const Expr* a,
                                                 const ScopeMap& scope) {
  switch (a->kind) {
    case ExprKind::kIntegerLiteral:
      return static_cast<int64_t>(ConstLiteralWidth(a));
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;
    case ExprKind::kIdentifier:
      return IdentifierBits(a, scope);
    case ExprKind::kBinary:
    case ExprKind::kUnary:
      return OperatorBits(a, scope);
    case ExprKind::kTernary:
      return TernaryBits(a, scope);
    default:
      return RangedKeywordBits(a, scope);
  }
}

std::optional<int64_t> EvalConstBits(const Expr* expr, const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return SelfDeterminedBits(expr->args[0], scope);
}

static const DataType* RegisteredNamedType(const DataType& type) {
  return g_typedefs == nullptr ? nullptr : FindNamedType(type, *g_typedefs);
}

static bool HeldInTwoStates(const DataType* type) {
  if (type == nullptr) return false;
  if (type->kind == DataTypeKind::kNamed)
    return RegisteredNamedType(*type) != nullptr &&
           !Is4stateType(*type, *g_typedefs);
  static const TypedefMap kNoTypedefs;
  return !Is4stateType(*type,
                       g_typedefs != nullptr ? *g_typedefs : kNoTypedefs);
}

static bool ReadsAName(const Expr* expr) {
  return expr->kind == ExprKind::kIdentifier ||
         expr->kind == ExprKind::kMemberAccess;
}

static bool UnknownBitsStayInPlace(const Expr* expr) {
  if (expr == nullptr) return true;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return !ExprContainsXZ(expr->repeat_count) &&
             std::all_of(expr->elements.begin(), expr->elements.end(),
                         UnknownBitsStayInPlace);
    case ExprKind::kIdentifier:
      return true;
    case ExprKind::kMemberAccess:
      return !ExprContainsXZ(expr);
    default:
      return !ExprContainsXZ(expr) && !AnySubExpr(expr, ReadsAName);
  }
}

static int g_param_refold_depth = 0;
static constexpr int kMaxParamRefoldDepth = 32;

static std::optional<ConstVal> RefoldParamValue(const RtlirParamDecl& pd) {
  const Expr* value_expr =
      pd.from_override ? LiteralOverrideExpr(pd) : pd.default_value;
  if (value_expr == nullptr || g_param_refold_depth >= kMaxParamRefoldDepth)
    return std::nullopt;
  ++g_param_refold_depth;
  struct DepthGuard {
    ~DepthGuard() { --g_param_refold_depth; }
  } depth_guard;
  return ConstEvalFull(value_expr, RegisteredModuleScope(),
                       DeclaredFoldContext(pd));
}

static std::optional<ConstVal> TwoStateReadingOf(const RtlirParamDecl& pd) {
  if (!UnknownDigitsReadAsZero()) return std::nullopt;
  if (HeldInTwoStates(pd.type_param_actual != nullptr ? pd.type_param_actual
                                                      : pd.decl_type))
    return std::nullopt;
  const Expr* value_expr =
      pd.from_override ? LiteralOverrideExpr(pd) : pd.default_value;
  if (value_expr == nullptr || !UnknownBitsStayInPlace(value_expr))
    return std::nullopt;
  return RefoldParamValue(pd);
}

static std::vector<uint64_t> HighWordsOfParam(
    const RtlirParamDecl& pd, const std::optional<ConstVal>& refold) {
  if (!pd.resolved_high_words.empty()) return pd.resolved_high_words;
  if (refold) return refold->high_words;
  return {};
}

struct ParamReadWidth {
  uint32_t width;
  bool is_signed;
};

static ParamReadWidth ReadWidthOf(const RtlirParamDecl& pd,
                                  const std::optional<ConstVal>& refold) {
  if (HasDeclaredWidth(pd)) return {pd.decl_width, pd.decl_is_signed};
  if (pd.value_width != 0) return {pd.value_width, pd.value_is_signed};
  if (refold) return {refold->width, refold->is_signed};
  return {32, true};
}

std::optional<ConstVal> RegisteredParamValue(std::string_view name,
                                             int64_t value) {
  const RtlirParamDecl* pd = RegisteredParamNamed(name);
  if (pd == nullptr || pd->resolved_value != value) return std::nullopt;
  bool declared = HasDeclaredWidth(*pd);
  bool recorded_width = declared || pd->value_width != 0;
  bool recorded_words = !pd->resolved_high_words.empty();
  std::optional<ConstVal> refold;
  if (!recorded_width || (pd->decl_width > 64 && !recorded_words))
    refold = RefoldParamValue(*pd);
  auto two_state = TwoStateReadingOf(*pd);
  if (two_state) {
    value = two_state->value;
    refold = two_state;
  }
  ParamReadWidth rw = ReadWidthOf(*pd, refold);
  ConstVal v = NormalizeConstVal(value, rw.width, rw.is_signed);
  if (rw.width > 64)
    v.high_words =
        two_state ? two_state->high_words : HighWordsOfParam(*pd, refold);
  return v;
}

FoldContext DeclaredFoldContext(const RtlirParamDecl& pd) {
  if (!HasDeclaredWidth(pd)) return {};
  return {pd.decl_width, false};
}

static std::optional<int64_t> FoldValueInContext(
    const Expr* expr, const ScopeMap& scope, FoldContext ctx,
    std::optional<bool> read_signed) {
  auto value = ConstEvalFull(expr, scope, ctx);
  if (!value) return std::nullopt;
  if (ctx.width == 0) return value->value;
  return CastConstVal(*value, ctx.width, read_signed.value_or(value->is_signed))
      .value;
}

static std::optional<int64_t> FoldConvertedToType(
    const Expr* expr, const DataType* type, const ScopeMap& scope,
    FoldContext ctx, std::optional<bool> read_signed) {
  TwoStateLiteralGuard guard(HeldInTwoStates(type) &&
                             UnknownBitsStayInPlace(expr));
  return FoldValueInContext(expr, scope, ctx, read_signed);
}

std::optional<int64_t> FoldParamValue(const RtlirParamDecl& pd,
                                      const Expr* expr, const ScopeMap& scope) {
  const DataType* type =
      pd.type_param_actual != nullptr ? pd.type_param_actual : pd.decl_type;
  return FoldConvertedToType(expr, type, scope, DeclaredFoldContext(pd),
                             std::nullopt);
}

uint32_t DeclaredParamTypeWidth(const DataType& type, const ScopeMap& scope) {
  if (type.kind == DataTypeKind::kNamed) {
    if (RegisteredNamedType(type) == nullptr) return 0;
    return EvalTypeWidth(type, *g_typedefs, scope);
  }
  if (type.packed_dim_left != nullptr) return PackedDimProduct(type, scope);
  if (type.kind == DataTypeKind::kImplicit) return 0;
  return EvalTypeWidth(type);
}

static bool DeclaredParamTypeIsSigned(const DataType& type) {
  if (type.kind != DataTypeKind::kNamed || type.packed_dim_left != nullptr)
    return type.is_signed;
  return RegisteredNamedType(type) != nullptr &&
         IsSignedType(type, *g_typedefs);
}

std::optional<int64_t> FoldDeclaredParamValue(const Expr* expr,
                                              const DataType& type,
                                              const ScopeMap& scope) {
  return FoldConvertedToType(
      expr, &type, scope,
      FoldContext{DeclaredParamTypeWidth(type, scope), false},
      DeclaredParamTypeIsSigned(type));
}

std::optional<int64_t> TwoStateReading(const Expr* expr, const DataType& type,
                                       const ScopeMap& scope, int64_t value) {
  if (HeldInTwoStates(&type) || !UnknownBitsStayInPlace(expr))
    return std::nullopt;
  TwoStateLiteralGuard guard(true);
  auto reading = FoldValueInContext(
      expr, scope, FoldContext{DeclaredParamTypeWidth(type, scope), false},
      DeclaredParamTypeIsSigned(type));
  if (!reading || *reading == value) return std::nullopt;
  return reading;
}

static std::string TwoStateReadingKey(std::string_view name) {
  return "$two_state::" + std::string(name);
}

static std::unordered_set<std::string>& TwoStateReadingKeys() {
  static std::unordered_set<std::string> keys;
  return keys;
}

void SetTwoStateReading(ScopeMap& scope, std::string_view name,
                        std::optional<int64_t> reading) {
  auto& keys = TwoStateReadingKeys();
  std::string key = TwoStateReadingKey(name);
  if (!reading) {
    scope.erase(key);
    return;
  }
  scope[*keys.insert(std::move(key)).first] = *reading;
}

void BindDeclaredConstant(ScopeMap& scope, std::string_view name,
                          int64_t value) {
  scope[name] = value;
  if (TwoStateReadingKeys().empty()) return;
  scope.erase(TwoStateReadingKey(name));
}

std::optional<int64_t> RecordedTwoStateReading(const ScopeMap& scope,
                                               std::string_view name) {
  auto it = scope.find(TwoStateReadingKey(name));
  if (it == scope.end()) return std::nullopt;
  return it->second;
}

std::optional<int64_t> FindTwoStateReading(const ScopeMap& scope,
                                           std::string_view name) {
  if (!UnknownDigitsReadAsZero()) return std::nullopt;
  return RecordedTwoStateReading(scope, name);
}

std::optional<int64_t> FoldParamValueAtWidth(const Expr* expr,
                                             const ScopeMap& scope,
                                             uint32_t width, bool is_signed) {
  return FoldValueInContext(expr, scope, FoldContext{width, false}, is_signed);
}

void RecordResolvedHighWords(RtlirParamDecl& pd, const Expr* expr,
                             const ScopeMap& scope) {
  pd.resolved_high_words.clear();
  pd.value_width = 0;
  pd.value_is_signed = false;
  if (expr == nullptr || pd.is_type_param || pd.is_real_value ||
      pd.is_string_value)
    return;
  bool declared = HasDeclaredWidth(pd);
  if (declared && pd.decl_width <= 64) return;
  auto folded = ConstEvalFull(expr, scope, DeclaredFoldContext(pd));
  if (!folded) return;
  uint32_t width = declared ? pd.decl_width : folded->width;
  bool is_signed = declared ? pd.decl_is_signed : folded->is_signed;
  ConstVal v = CastConstVal(*folded, width, is_signed);
  if (v.value != pd.resolved_value) return;
  if (!declared) {
    pd.value_width = width;
    pd.value_is_signed = is_signed;
  }
  pd.resolved_high_words = std::move(v.high_words);
}

}  // namespace delta
