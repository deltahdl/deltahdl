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

// Set the bit at `pos`, growing the container to reach it. §5.7.1 sizes a
// literal by its own size constant, so how far the digits reach is not known
// before they are read.
static void SetPatternBit(std::vector<bool>& bits, uint32_t pos) {
  if (bits.size() <= pos) bits.resize(pos + 1, false);
  bits[pos] = true;
}

bool PatternBitValue(const PatternBits& bits, uint32_t b) {
  return b < bits.aval.size() && bits.aval[b];
}

// True where §12.5.1 leaves bit position `b` of the pattern out of the
// comparison.
static bool PatternBitIsDontCare(const PatternBits& bits, uint32_t b) {
  if (bits.all_dont_care) return true;
  return b < bits.dc_mask.size() && bits.dc_mask[b];
}

static std::string StripPatternSeparators(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_' && c != ' ' && c != '\t') buf.push_back(c);
  }
  return buf;
}

// Decimal literals carry no per-bit data, so any z/? (or x under casex) makes
// the entire pattern don't-care. Returns true if such a token was found and
// the result was set accordingly.
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

// §5.7.1: multiplies the magnitude `words` holds, least significant word
// first, by 10 and adds `digit`, growing by a word when the product carries
// out of the top one. Each word is multiplied in 32-bit halves so the carry
// between them needs no integer wider than 64 bits.
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

// §5.7.1: the bits the decimal digits of `buf` from `start` form, however many
// the value needs: `80'd1208925819614629174706177` (2^80 + 1) writes bits 80
// and 0. Expr::int_val holds the value's low 64 bits alone, so the digits are
// read again here. The fold ends at the first character that is no decimal
// digit, which is where an x, z or ? digit stands.
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

// True if char c marks a don't-care digit under the given case kind. Under
// casez only z/?/Z is don't-care; otherwise x/X is don't-care too.
static bool IsDontCareDigit(char c, TokenKind case_kind) {
  bool is_z = (c == 'z' || c == 'Z' || c == '?');
  bool is_x = (c == 'x' || c == 'X');
  return (case_kind == TokenKind::kKwCasez) ? is_z : (is_z || is_x);
}

// Numeric value of a single binary/octal/hex digit character.
static uint64_t DigitCharValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return 0;
}

// Mark all bits contributed by one don't-care digit at bit_pos in the mask.
static void MarkDontCareBits(uint32_t bit_pos, int bits_per_digit,
                             PatternBits& result) {
  for (int b = 0; b < bits_per_digit; ++b)
    SetPatternBit(result.dc_mask, bit_pos + static_cast<uint32_t>(b));
}

// OR one decoded digit value (dv) into aval starting at bit_pos.
static void SetDigitValueBits(uint64_t dv, uint32_t bit_pos, int bits_per_digit,
                              PatternBits& result) {
  for (int b = 0; b < bits_per_digit; ++b) {
    if ((dv >> b) & 1u)
      SetPatternBit(result.aval, bit_pos + static_cast<uint32_t>(b));
  }
}

static void DecodePatternDigits(const std::string& buf, size_t i,
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
}

PatternBits ParsePatternLiteral(std::string_view text, TokenKind case_kind) {
  PatternBits result{};
  std::string buf = StripPatternSeparators(text);
  auto tick = buf.find('\'');
  // §5.7.1's first form, a simple decimal number: every character is a digit.
  if (tick == std::string::npos) {
    DecodeDecimalDigits(buf, 0, result);
    return result;
  }

  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  if (i >= buf.size()) return result;

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
      // A don't-care decimal is don't-care throughout; any other is folded
      // from its digits, so a value past 64 bits keeps its high bits.
      if (!ScanDecimalForDontCare(buf, i + 1, case_kind, result))
        DecodeDecimalDigits(buf, i + 1, result);
      return result;
    default:
      return result;
  }
  ++i;

  result.has_digits = true;
  DecodePatternDigits(buf, i, bits_per_digit, case_kind, result);
  return result;
}

// One case-item pattern (§12.5.1 casez/casez wildcards) after decoding: the
// source literal expression plus its decoded aval/dc_mask and whether wildcard
// decoding applies at all.
struct DecodedPattern {
  const Expr* pat;
  PatternBits bits;
  bool has_dc;
};

static uint32_t PatternBitLit(const LowerCtx& ctx, const DecodedPattern& pat,
                              uint32_t b) {
  // The decoding answers the pattern only where the literal was written with a
  // base giving each digit its own bits. A decimal literal writes none, so its
  // value is the one SynthLower::LowerExprBit reads.
  if (pat.has_dc && pat.bits.has_digits) {
    return PatternBitValue(pat.bits, b) ? AigGraph::kConstTrue
                                        : AigGraph::kConstFalse;
  }
  return ctx.synth.LowerExprBit(pat.pat, ctx.aig, b);
}

// True for the value range §11.4.13 writes as `[lo:hi]`.
// Parser::ParseInsideValueRange in src/parser/expr_parser_patterns.cpp
// builds it as an ExprKind::kSelect carrying both bounds and no base, which is
// what tells it from a bit-select or part-select of a signal. Compared bit for
// bit it would answer no run of bits, and so constant false at every position,
// making the item match exactly where the selector is zero.
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
    uint32_t sb = ctx.synth.LowerExprBit(sel_expr, ctx.aig, b);
    uint32_t pb = PatternBitLit(ctx, dp, b);
    eq = ctx.aig.AddAnd(eq, ctx.aig.AddNot(ctx.aig.AddXor(sb, pb)));
  }
  return eq;
}

}  // namespace delta
