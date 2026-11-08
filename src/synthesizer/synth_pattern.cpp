#include "synthesizer/synth_pattern.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static void SetPatternBit(std::vector<bool>& bits, uint32_t pos) {
  if (bits.size() <= pos) bits.resize(pos + 1, false);
  bits[pos] = true;
}

bool PatternBitValue(const PatternBits& bits, uint32_t b) {
  return b < bits.aval.size() && bits.aval[b];
}

static bool PatternBitIsDontCare(const PatternBits& bits, uint32_t b) {
  if (bits.all_dont_care) return true;
  if (b < bits.dc_mask.size()) return bits.dc_mask[b];
  return bits.dont_care_above;
}

static std::string StripPatternSeparators(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_' && c != ' ' && c != '\t') buf.push_back(c);
  }
  return buf;
}

static bool ScanDecimalForDontCare(const std::string& buf, size_t start,
                                   TokenKind case_kind, PatternBits& result) {
  for (size_t j = start; j < buf.size(); ++j) {
    char c = buf[j];
    bool is_z = (c == 'z' || c == 'Z' || c == '?');
    bool is_x = (c == 'x' || c == 'X');
    if (is_z || (is_x && case_kind == TokenKind::kKwCasex)) {
      result.all_dont_care = true;
      return true;
    }
  }
  return false;
}

static void MulTenAdd(std::vector<uint64_t>& words, uint64_t digit) {
  uint64_t carry = digit;
  for (uint64_t& w : words) {
    uint64_t lo = (w & 0xFFFFFFFFu) * 10 + carry;
    uint64_t hi = (w >> 32) * 10 + (lo >> 32);
    w = (hi << 32) | (lo & 0xFFFFFFFFu);
    carry = hi >> 32;
  }
  if (carry != 0) words.push_back(carry);
}

static void DecodeDecimalDigits(const std::string& buf, size_t start,
                                PatternBits& result) {
  std::vector<uint64_t> words{0};
  for (size_t j = start; j < buf.size(); ++j) {
    char c = buf[j];
    if (c < '0' || c > '9') break;
    MulTenAdd(words, static_cast<uint64_t>(c - '0'));
  }
  for (size_t w = 0; w < words.size(); ++w) {
    for (uint32_t b = 0; b < 64; ++b) {
      if ((words[w] >> b) & 1u)
        SetPatternBit(result.aval, static_cast<uint32_t>(w * 64) + b);
    }
  }
  result.has_digits = true;
}

static bool IsDontCareDigit(char c, TokenKind case_kind) {
  bool is_z = (c == 'z' || c == 'Z' || c == '?');
  bool is_x = (c == 'x' || c == 'X');
  return (case_kind == TokenKind::kKwCasez) ? is_z : (is_z || is_x);
}

static uint64_t DigitCharValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return 0;
}

static void MarkDontCareBits(uint32_t bit_pos, int bits_per_digit,
                             PatternBits& result) {
  for (int b = 0; b < bits_per_digit; ++b)
    SetPatternBit(result.dc_mask, bit_pos + static_cast<uint32_t>(b));
}

static void SetDigitValueBits(uint64_t dv, uint32_t bit_pos, int bits_per_digit,
                              PatternBits& result) {
  for (int b = 0; b < bits_per_digit; ++b) {
    if ((dv >> b) & 1u)
      SetPatternBit(result.aval, bit_pos + static_cast<uint32_t>(b));
  }
}

static uint32_t DecodePatternDigits(const std::string& buf, size_t i,
                                    int bits_per_digit, TokenKind case_kind,
                                    PatternBits& result) {
  uint32_t bit_pos = 0;
  for (size_t j = buf.size(); j > i; --j) {
    char c = buf[j - 1];
    if (IsDontCareDigit(c, case_kind)) {
      MarkDontCareBits(bit_pos, bits_per_digit, result);
    } else {
      SetDigitValueBits(DigitCharValue(c), bit_pos, bits_per_digit, result);
    }
    bit_pos += bits_per_digit;
  }
  return bit_pos;
}

static void PadWithDontCare(uint32_t top, uint32_t size, PatternBits& result) {
  if (size == 0) {
    result.dont_care_above = true;
    return;
  }
  if (top < size) MarkDontCareBits(top, static_cast<int>(size - top), result);
}

static uint32_t PatternSizeConstant(const std::string& buf, size_t tick) {
  uint32_t size = 0;
  for (size_t j = 0; j < tick; ++j) {
    size = size * 10 + static_cast<uint32_t>(buf[j] - '0');
  }
  return size;
}

static void TruncateToSize(PatternBits& result, uint32_t size) {
  if (size == 0) return;
  if (result.aval.size() > size) result.aval.resize(size);
  if (result.dc_mask.size() > size) result.dc_mask.resize(size);
}

static void DecodeBasedLiteral(const std::string& buf, size_t tick,
                               uint32_t size, TokenKind case_kind,
                               PatternBits& result) {
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  if (i >= buf.size()) return;

  int bits_per_digit = 0;
  switch (buf[i]) {
    case 'b':
    case 'B':
      bits_per_digit = 1;
      break;
    case 'o':
    case 'O':
      bits_per_digit = 3;
      break;
    case 'h':
    case 'H':
      bits_per_digit = 4;
      break;
    case 'd':
    case 'D':
      if (!ScanDecimalForDontCare(buf, i + 1, case_kind, result))
        DecodeDecimalDigits(buf, i + 1, result);
      return;
    default:
      return;
  }
  ++i;

  result.has_digits = true;
  uint32_t top = DecodePatternDigits(buf, i, bits_per_digit, case_kind, result);
  if (i < buf.size() && IsDontCareDigit(buf[i], case_kind))
    PadWithDontCare(top, size, result);
}

PatternBits ParsePatternLiteral(std::string_view text, TokenKind case_kind) {
  PatternBits result{};
  std::string buf = StripPatternSeparators(text);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) {
    DecodeDecimalDigits(buf, 0, result);
    return result;
  }
  uint32_t size = PatternSizeConstant(buf, tick);
  DecodeBasedLiteral(buf, tick, size, case_kind, result);
  TruncateToSize(result, size);
  return result;
}

struct DecodedPattern {
  const Expr* pat;
  PatternBits bits;
  bool has_dc;
};

static uint32_t PatternBitLit(const LowerCtx& ctx, const DecodedPattern& pat,
                              uint32_t b) {
  if (pat.has_dc && pat.bits.has_digits) {
    return PatternBitValue(pat.bits, b) ? AigGraph::kConstTrue
                                        : AigGraph::kConstFalse;
  }
  return ctx.synth.LowerExprBit(pat.pat, ctx.aig, b);
}

static bool IsValueRange(const Expr* pat) {
  return pat->kind == ExprKind::kSelect && pat->base == nullptr;
}

uint32_t BuildPatternMatch(const Expr* sel_expr, const Expr* pat,
                           const LowerCtx& ctx, uint32_t sel_width,
                           TokenKind case_kind) {
  if (IsValueRange(pat)) {
    return ctx.synth.LowerInsideRangeMatch(sel_expr, pat, ctx.aig, sel_width);
  }
  DecodedPattern dp{pat, PatternBits{},
                    (case_kind != TokenKind::kKwCase) &&
                        (pat->kind == ExprKind::kIntegerLiteral)};
  if (dp.has_dc) dp.bits = ParsePatternLiteral(pat->text, case_kind);

  uint32_t eq = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < sel_width; ++b) {
    if (dp.has_dc && PatternBitIsDontCare(dp.bits, b)) continue;
    uint32_t sb = ctx.synth.LowerContextOperandBit(sel_expr, ctx.aig, b);
    uint32_t pb = PatternBitLit(ctx, dp, b);
    eq = ctx.aig.AddAnd(eq, ctx.aig.AddNot(ctx.aig.AddXor(sb, pb)));
  }
  return eq;
}

}  // namespace delta
