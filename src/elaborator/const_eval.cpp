#include "elaborator/const_eval.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"

namespace delta {

bool SizedByLeftOperand(TokenKind op) {
  switch (op) {
    case TokenKind::kLtLt:
    case TokenKind::kLtLtEq:
    case TokenKind::kLtLtLt:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGt:
    case TokenKind::kGtGtEq:
    case TokenKind::kGtGtGt:
    case TokenKind::kGtGtGtEq:
    case TokenKind::kPower:
      return true;
    default:
      return false;
  }
}

bool BinaryResultSigned(TokenKind op, const ConstVal& lhs,
                        const ConstVal& rhs) {
  return lhs.is_signed && (SizedByLeftOperand(op) || rhs.is_signed);
}

static std::optional<int64_t> EvalBinaryArith(TokenKind op, int64_t lhs,
                                              int64_t rhs) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kPlusEq:
      return lhs + rhs;
    case TokenKind::kMinus:
    case TokenKind::kMinusEq:
      return lhs - rhs;
    case TokenKind::kStar:
    case TokenKind::kStarEq:
      return lhs * rhs;
    case TokenKind::kSlash:
    case TokenKind::kSlashEq:
      if (rhs == 0) return std::nullopt;
      if (rhs == -1) return static_cast<int64_t>(-static_cast<uint64_t>(lhs));
      return lhs / rhs;
    case TokenKind::kPercent:
    case TokenKind::kPercentEq:
      if (rhs == 0) return std::nullopt;
      if (rhs == -1) return 0;
      return lhs % rhs;
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinaryBitwise(TokenKind op, int64_t lhs,
                                                int64_t rhs) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kAmpEq:
      return lhs & rhs;
    case TokenKind::kPipe:
    case TokenKind::kPipeEq:
      return lhs | rhs;
    case TokenKind::kCaret:
    case TokenKind::kCaretEq:
      return lhs ^ rhs;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return ~(lhs ^ rhs);
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinaryCompare(TokenKind op, int64_t lhs,
                                                int64_t rhs) {
  switch (op) {
    case TokenKind::kLt:
      return static_cast<int64_t>(lhs < rhs);
    case TokenKind::kGt:
      return static_cast<int64_t>(lhs > rhs);
    case TokenKind::kLtEq:
      return static_cast<int64_t>(lhs <= rhs);
    case TokenKind::kGtEq:
      return static_cast<int64_t>(lhs >= rhs);
    case TokenKind::kEqEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kEqEqQuestion:
      return static_cast<int64_t>(lhs == rhs);
    case TokenKind::kBangEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kBangEqQuestion:
      return static_cast<int64_t>(lhs != rhs);
    case TokenKind::kAmpAmp:
      return static_cast<int64_t>(lhs != 0 && rhs != 0);
    case TokenKind::kPipePipe:
      return static_cast<int64_t>(lhs != 0 || rhs != 0);
    case TokenKind::kArrow:
      return static_cast<int64_t>(lhs == 0 || rhs != 0);
    case TokenKind::kLtDashGt:
      return static_cast<int64_t>((lhs != 0) == (rhs != 0));
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinary(TokenKind op, int64_t lhs,
                                         int64_t rhs) {
  auto result = EvalBinaryArith(op, lhs, rhs);
  if (result) return result;
  result = EvalBinaryBitwise(op, lhs, rhs);
  if (result) return result;
  return EvalBinaryCompare(op, lhs, rhs);
}

static std::optional<int64_t> EvalUnary(TokenKind op, int64_t operand) {
  switch (op) {
    case TokenKind::kMinus:
      return -operand;
    case TokenKind::kPlus:
      return operand;
    case TokenKind::kTilde:
      return ~operand;
    default:
      return std::nullopt;
  }
}

static bool SizedByOperand(TokenKind op) {
  return op == TokenKind::kMinus || op == TokenKind::kPlus ||
         op == TokenKind::kTilde;
}

uint32_t ConstLiteralWidth(const Expr* expr) {
  if (expr->text.empty()) return 32;
  return LiteralWidth(expr->text, expr->int_val);
}

static int64_t Clog2(int64_t val) {
  auto v = static_cast<uint64_t>(val);
  if (v <= 1) return 0;
  int64_t result = 0;
  uint64_t shifted = v - 1;
  while (shifted > 0) {
    shifted >>= 1;
    ++result;
  }
  return result;
}

static int64_t Countones(int64_t val) {
  auto u = static_cast<uint64_t>(val);
  int64_t count = 0;
  while (u != 0) {
    u &= u - 1;
    ++count;
  }
  return count;
}

static std::optional<int64_t> EvalFirstArg(const Expr* expr,
                                           const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return ConstEvalInt(expr->args[0], scope);
}

const RtlirParamDecl* RegisteredParamNamed(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return nullptr;
  for (const auto& param : mod->params) {
    if (param.name != name) continue;
    if (!ParamVisibleFromScopes(param.gen_block_prefix,
                                RegisteredGenPrefixes()))
      continue;
    return &param;
  }
  return nullptr;
}

static bool ControlBitIsXZ(const Expr* ctrl) {
  if (!ctrl || ctrl->kind != ExprKind::kIntegerLiteral) return false;
  auto t = ctrl->text;
  auto tick = t.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < t.size(); ++i) {
    char c = t[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

static int64_t CountonesInWidth(int64_t val, uint32_t width) {
  uint64_t mask =
      (width == 0 || width >= 64) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1);
  return Countones(static_cast<int64_t>(static_cast<uint64_t>(val) & mask));
}

static std::optional<int64_t> EvalConstCountbits(const Expr* expr,
                                                 const ScopeMap& scope) {
  if (expr->args.size() < 2) return std::nullopt;
  auto val = ConstEvalInt(expr->args[0], scope);
  if (!val) return std::nullopt;
  uint32_t width = ConstLiteralWidth(expr->args[0]);
  bool match0 = false;
  bool match1 = false;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto* ctrl = expr->args[i];
    if (ControlBitIsXZ(ctrl)) continue;
    auto cb = ConstEvalInt(ctrl, scope);
    if (!cb) return std::nullopt;
    if ((*cb & 1) == 0) {
      match0 = true;
    } else {
      match1 = true;
    }
  }
  int64_t ones = CountonesInWidth(*val, width);
  int64_t total = (width >= 64) ? 64 : static_cast<int64_t>(width);
  int64_t zeros = total - ones;
  int64_t result = 0;
  if (match1) result += ones;
  if (match0) result += zeros;
  return result;
}

static std::optional<int64_t> EvalConstRealToIntCall(const Expr* expr,
                                                     const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  auto rv = ConstEvalReal(expr->args[0], scope);
  if (!rv) return std::nullopt;
  if (expr->callee == "$rtoi")
    return static_cast<int32_t>(static_cast<int64_t>(*rv));
  if (expr->callee == "$realtobits") {
    double d = *rv;
    uint64_t bits = 0;
    std::memcpy(&bits, &d, sizeof(d));
    return static_cast<int64_t>(bits);
  }
  auto fv = static_cast<float>(*rv);
  uint32_t bits = 0;
  std::memcpy(&bits, &fv, sizeof(fv));
  return static_cast<int64_t>(bits);
}

std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                        const ScopeMap& scope) {
  if (expr->callee == "$bits") return EvalConstBits(expr, scope);
  if (IsArrayQueryFunction(expr->callee)) {
    return EvalConstArrayQuery(expr, scope);
  }
  if (expr->callee == "$countbits") return EvalConstCountbits(expr, scope);
  if (expr->callee == "$rtoi" || expr->callee == "$realtobits" ||
      expr->callee == "$shortrealtobits")
    return EvalConstRealToIntCall(expr, scope);
  auto arg = EvalFirstArg(expr, scope);
  if (!arg) return std::nullopt;
  if (expr->callee == "$clog2") return Clog2(*arg);
  if (expr->callee == "$countones") return Countones(*arg);
  if (expr->callee == "$onehot")
    return static_cast<int64_t>(Countones(*arg) == 1);
  if (expr->callee == "$onehot0")
    return static_cast<int64_t>(Countones(*arg) <= 1);
  if (expr->callee == "$isunknown") return 0;
  return std::nullopt;
}

static int64_t TruncateToWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  return static_cast<int64_t>(static_cast<uint64_t>(val) &
                              ((uint64_t{1} << width) - 1));
}

static int64_t SignExtendFromWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  uint64_t mask = (uint64_t{1} << width) - 1;
  uint64_t uval = static_cast<uint64_t>(val) & mask;
  if (uval & (uint64_t{1} << (width - 1))) {
    uval |= ~mask;
  }
  return static_cast<int64_t>(uval);
}

ConstVal NormalizeConstVal(int64_t value, uint32_t width, bool is_signed) {
  int64_t v = TruncateToWidth(value, width);
  if (is_signed) v = SignExtendFromWidth(v, width);
  return ConstVal{v, width, is_signed};
}

std::optional<ConstVal> ConstEvalLiteral(const Expr* expr) {
  uint32_t width = ConstLiteralWidth(expr);
  uint64_t low = expr->int_val;
  if (UnknownDigitsReadAsZero())
    low = BasedLiteralLowWord(expr->text).value_or(low);
  ConstVal v = NormalizeConstVal(static_cast<int64_t>(low), width,
                                 IsSignedLiteral(expr->text));
  v.high_words = LiteralHighWords(expr->text, width);
  return v;
}

std::optional<ConstVal> ConstEvalUnbasedUnsized(const Expr* expr,
                                                FoldContext ctx) {
  uint32_t width = ctx.width > 0 ? ctx.width : 1;
  bool ones = expr->text.size() >= 2 && expr->text[1] == '1';
  std::vector<uint64_t> words((width + 63) / 64, ones ? ~uint64_t{0} : 0);
  ClearBitsFrom(words, width);
  return ConstValOfWords(words, width, false);
}

static int ConstHexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static bool ConstDecodeEscape(std::string_view text, size_t& i, uint8_t& out) {
  char c = text[i];
  switch (c) {
    case 'n':
      out = '\n';
      return true;
    case 't':
      out = '\t';
      return true;
    case '\\':
      out = '\\';
      return true;
    case '"':
      out = '"';
      return true;
    case 'v':
      out = '\v';
      return true;
    case 'f':
      out = '\f';
      return true;
    case 'a':
      out = '\a';
      return true;
    default:
      break;
  }
  if (c == '\n') return false;
  if (c == 'x') {
    uint8_t val = 0;
    for (int j = 0; j < 2 && i + 1 < text.size(); ++j) {
      int d = ConstHexDigitVal(text[i + 1]);
      if (d < 0) break;
      val = static_cast<uint8_t>(val * 16 + d);
      ++i;
    }
    out = val;
    return true;
  }
  if (c >= '0' && c <= '7') {
    auto val = static_cast<uint8_t>(c - '0');
    for (int j = 0; j < 2 && i + 1 < text.size() && text[i + 1] >= '0' &&
                    text[i + 1] <= '7';
         ++j) {
      val = static_cast<uint8_t>(val * 8 + (text[++i] - '0'));
    }
    out = val;
    return true;
  }
  out = static_cast<uint8_t>(c);
  return true;
}

static std::string StringLiteralBytes(const Expr* expr) {
  std::string_view text = StringLiteralBody(expr->text);
  std::string bytes;
  for (size_t i = 0; i < text.size(); ++i) {
    uint8_t byte = 0;
    if (text[i] == '\\' && i + 1 < text.size()) {
      ++i;
      if (!ConstDecodeEscape(text, i, byte)) continue;
    } else {
      byte = static_cast<uint8_t>(text[i]);
    }
    bytes.push_back(static_cast<char>(byte));
  }
  return bytes;
}

static std::string StringLiteralChars(const Expr* expr) {
  std::string chars = StringLiteralBytes(expr);
  std::erase(chars, '\0');
  return chars;
}

static std::optional<std::string> StringParamChars(const Expr* expr) {
  const RtlirParamDecl* param = RegisteredParamNamed(expr->text);
  if (param == nullptr || !param->is_string_value) return std::nullopt;
  return std::string(param->resolved_string);
}

ScopeMap RegisteredModuleScope() {
  ScopeMap scope;
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return scope;
  for (const auto& param : mod->params) {
    if (!param.is_resolved) continue;
    if (!param.gen_block_prefix.empty()) continue;
    scope[param.name] = param.resolved_value;
  }
  return scope;
}

static std::optional<std::string> ConcatenatedStringChars(const Expr* expr) {
  std::string chars;
  for (const Expr* element : expr->elements) {
    auto part = ConstEvalString(element);
    if (!part) return std::nullopt;
    chars += *part;
  }
  return chars;
}

static std::optional<std::string> ReplicatedStringChars(const Expr* expr) {
  auto count = ConstEvalInt(expr->repeat_count, RegisteredModuleScope());
  if (!count || *count < 0) return std::nullopt;
  auto inner = ConcatenatedStringChars(expr);
  if (!inner) return std::nullopt;
  std::string chars;
  for (int64_t i = 0; i < *count; ++i) chars += *inner;
  return chars;
}

std::optional<std::string> ConstEvalString(const Expr* expr) {
  if (expr == nullptr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kStringLiteral:
      return StringLiteralChars(expr);
    case ExprKind::kIdentifier:
      return StringParamChars(expr);
    case ExprKind::kConcatenation:
      return ConcatenatedStringChars(expr);
    case ExprKind::kReplicate:
      return ReplicatedStringChars(expr);
    case ExprKind::kSystemCall:
      return ConstTypenameChars(expr);
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
      return ConstEvalAggregatePartString(expr, RegisteredModuleScope());
    default:
      return std::nullopt;
  }
}

std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr) {
  auto chars = expr->kind == ExprKind::kStringLiteral
                   ? std::optional<std::string>(StringLiteralBytes(expr))
                   : ConstEvalString(expr);
  if (!chars) return std::nullopt;
  uint32_t width =
      chars->empty() ? 8u : static_cast<uint32_t>(chars->size()) * 8u;
  std::vector<uint64_t> words((width + 63) / 64, 0);
  const size_t kCount = chars->size();
  for (size_t i = 0; i < kCount; ++i) {
    const size_t kByte = kCount - 1 - i;
    words[kByte / 8] |= uint64_t{static_cast<uint8_t>((*chars)[i])}
                        << (8 * (kByte % 8));
  }
  return ConstValOfWords(words, width, false);
}

static std::optional<int64_t> ReduceConstVal(TokenKind op, const ConstVal& v) {
  bool all = true;
  bool any = false;
  bool odd = false;
  for (uint32_t i = 0; i < v.width; ++i) {
    const bool kBit = ConstValBit(v, i);
    all = all && kBit;
    any = any || kBit;
    odd = odd != kBit;
  }
  switch (op) {
    case TokenKind::kAmp:
      return all;
    case TokenKind::kTildeAmp:
      return !all;
    case TokenKind::kPipe:
      return any;
    case TokenKind::kTildePipe:
      return !any;
    case TokenKind::kCaret:
      return odd;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return !odd;
    default:
      return std::nullopt;
  }
}

std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                           const ScopeMap& scope,
                                           FoldContext ctx) {
  auto operand = ConstEvalFull(expr->lhs, scope,
                               SizedByOperand(expr->op) ? ctx : FoldContext{});
  if (!operand) return std::nullopt;
  if (expr->op == TokenKind::kBang)
    return ConstVal{ConstValIsNonZero(*operand) ? 0 : 1, 1, false};
  if (auto reduced = ReduceConstVal(expr->op, *operand))
    return ConstVal{*reduced, 1, false};
  if (operand->width > 64) {
    if (auto wide = EvalWideUnary(expr->op, *operand)) return wide;
  }
  if (expr->op == TokenKind::kMinus) {
    return NormalizeConstVal(-operand->value, operand->width,
                             operand->is_signed);
  }
  auto result = EvalUnary(expr->op, operand->value);
  if (!result) return std::nullopt;
  int64_t v = TruncateToWidth(*result, operand->width);
  if (operand->is_signed) v = SignExtendFromWidth(v, operand->width);
  return ConstVal{v, operand->width, operand->is_signed};
}

static void NormalizeBinaryOperands(const ConstVal& lhs, const ConstVal& rhs,
                                    bool is_signed, int64_t& lv, int64_t& rv) {
  if (is_signed) {
    lv = SignExtendFromWidth(lhs.value, lhs.width);
    rv = SignExtendFromWidth(rhs.value, rhs.width);
  } else {
    lv = TruncateToWidth(lhs.value, lhs.width);
    rv = TruncateToWidth(rhs.value, rhs.width);
  }
}

static std::optional<ConstVal> EvalUnsignedDivMod(TokenKind op, int64_t lv,
                                                  int64_t rv, uint32_t width,
                                                  bool& handled) {
  handled = true;
  auto ul = static_cast<uint64_t>(lv);
  auto ur = static_cast<uint64_t>(rv);
  if (op == TokenKind::kSlash || op == TokenKind::kSlashEq) {
    if (ur == 0) return std::nullopt;
    return ConstVal{static_cast<int64_t>(ul / ur), width, false};
  }
  if (op == TokenKind::kPercent || op == TokenKind::kPercentEq) {
    if (ur == 0) return std::nullopt;
    return ConstVal{static_cast<int64_t>(ul % ur), width, false};
  }
  handled = false;
  return std::nullopt;
}

static std::optional<ConstVal> FoldDecidedByFirstOperand(
    const Expr* expr, const ScopeMap& scope) {
  const bool kOr = expr->op == TokenKind::kPipePipe;
  if (!kOr && expr->op != TokenKind::kAmpAmp && expr->op != TokenKind::kArrow)
    return std::nullopt;
  auto first = ConstEvalFull(expr->lhs, scope);
  if (!first) return std::nullopt;
  if (ConstValIsNonZero(*first) != kOr) return std::nullopt;
  return ConstVal{expr->op == TokenKind::kAmpAmp ? 0 : 1, 1, false};
}

std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                            const ScopeMap& scope,
                                            FoldContext ctx) {
  if (auto matched = RegisteredTypeRefCompare(expr))
    return ConstVal{*matched, 1, false};
  if (auto decided = FoldDecidedByFirstOperand(expr, scope)) return decided;
  auto operands = FoldBinaryOperands(expr, scope, ctx);
  if (!operands) return std::nullopt;
  const ConstVal& lhs = operands->lhs;
  const ConstVal& rhs = operands->rhs;
  bool left_sized = SizedByLeftOperand(expr->op);
  uint32_t w = left_sized ? lhs.width : std::max(lhs.width, rhs.width);
  if (left_sized || w > 64) {
    auto wide = EvalWideBinary(expr->op, lhs, rhs, w);
    if (wide || left_sized) return wide;
  }
  bool s = BinaryResultSigned(expr->op, lhs, rhs);
  int64_t lv = 0, rv = 0;
  NormalizeBinaryOperands(lhs, rhs, s, lv, rv);
  if (!s) {
    bool handled = false;
    auto div_result = EvalUnsignedDivMod(expr->op, lv, rv, w, handled);
    if (handled) return div_result;
  }
  auto result = EvalBinary(expr->op, lv, rv);
  if (!result) return std::nullopt;
  if (AnswersOneBit(expr->op)) return ConstVal{*result, 1, false};
  return NormalizeConstVal(*result, w, s);
}

static std::optional<PackedRange> SelectBaseRange(const Expr* base,
                                                  const ScopeMap& scope) {
  if (base->kind != ExprKind::kIdentifier)
    return AggregatePartRange(base, scope);
  return RegisteredParamRange(base->text);
}

static int64_t SelectOffset(const std::optional<PackedRange>& range,
                            int64_t index) {
  return range ? range->OffsetOf(index) : index;
}

static bool InsideValue(const ConstVal& value, int64_t offset) {
  return offset >= 0 && offset < static_cast<int64_t>(value.width);
}

static std::optional<ConstVal> SelectOneBit(const ConstVal& value,
                                            int64_t offset) {
  if (!InsideValue(value, offset)) return std::nullopt;
  return ConstVal{ConstValBit(value, offset) ? 1 : 0, 1, false};
}

static std::optional<ConstVal> SelectBitRange(const ConstVal& value,
                                              int64_t off_a, int64_t off_b) {
  const int64_t kHi = std::max(off_a, off_b);
  const int64_t kLo = std::min(off_a, off_b);
  if (!InsideValue(value, kLo) || !InsideValue(value, kHi)) return std::nullopt;
  const auto kWidth = static_cast<uint32_t>(kHi - kLo + 1);
  std::vector<uint64_t> words((kWidth + 63) / 64, 0);
  for (uint32_t i = 0; i < kWidth; ++i) {
    if (ConstValBit(value, kLo + i)) words[i / 64] |= uint64_t{1} << (i % 64);
  }
  return ConstValOfWords(words, kWidth, false);
}

std::optional<ConstVal> ConstEvalSelectFull(const Expr* expr,
                                            const ScopeMap& scope) {
  if (auto element = ConstEvalAggregatePart(expr, scope)) return element;
  auto base_val = ConstEvalFull(expr->base, scope);
  if (!base_val) return std::nullopt;
  auto idx = ConstEvalFull(expr->index, scope);
  if (!idx) return std::nullopt;
  auto range = SelectBaseRange(expr->base, scope);
  if (expr->index_end) {
    auto end = ConstEvalFull(expr->index_end, scope);
    if (!end) return std::nullopt;
    int64_t last = end->value;
    if (expr->is_part_select_plus) last = idx->value + end->value - 1;
    if (expr->is_part_select_minus) last = idx->value - end->value + 1;
    return SelectBitRange(*base_val, SelectOffset(range, idx->value),
                          SelectOffset(range, last));
  }
  return SelectOneBit(*base_val, SelectOffset(range, idx->value));
}

}  // namespace delta
