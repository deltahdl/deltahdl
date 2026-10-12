#include <algorithm>
#include <array>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

uint64_t WidthMask(uint32_t width) {
  return width == 0 || width >= 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
}

// The bits per digit of the based literal base `base`, 0 for a decimal one.
unsigned BitsPerDigit(char base) {
  switch (std::tolower(static_cast<unsigned char>(base))) {
    case 'b':
      return 1;
    case 'o':
      return 3;
    case 'h':
      return 4;
    default:
      return 0;
  }
}

bool IsWildDigit(char c, bool with_x) {
  return c == '?' || c == 'z' || c == 'Z' || (with_x && (c == 'x' || c == 'X'));
}

// The bits the digits `digits` of a based literal, each `bits` wide, write as
// x, z or `?` (IsWildDigit), the leftmost such digit filling every bit above
// it.
uint64_t DigitXzBits(std::string_view digits, unsigned bits, bool with_x) {
  uint64_t mask = 0;
  unsigned shift = 0;
  bool leftmost_wild = false;
  for (auto it = digits.rbegin(); it != digits.rend() && shift < 64; ++it) {
    if (*it == '_' || *it == ' ') continue;
    leftmost_wild = IsWildDigit(*it, with_x);
    if (leftmost_wild) mask |= ((uint64_t{1} << bits) - 1) << shift;
    shift += bits;
  }
  if (leftmost_wild && shift < 64) mask |= ~uint64_t{0} << shift;
  return mask;
}

// §5.7.1: the bits of the integer literal `e` its digits write as z or `?`,
// and as x where `with_x`; a leftmost such digit fills every bit above it, and
// a decimal literal's one such digit every bit. A constant value holds no x or
// z (ConstVal), so these bits fold to 0 and are known only from the digits.
uint64_t LiteralXzBits(const Expr* e, bool with_x) {
  if (e == nullptr || e->kind != ExprKind::kIntegerLiteral) return 0;
  std::string_view t = e->text;
  size_t pos = t.find('\'');
  if (pos == std::string_view::npos) return 0;
  ++pos;
  if (pos < t.size() && (t[pos] == 's' || t[pos] == 'S')) ++pos;
  if (pos >= t.size()) return 0;
  const unsigned kBits = BitsPerDigit(t[pos++]);
  std::string_view digits = t.substr(pos);
  if (kBits == 0) {
    return std::any_of(digits.begin(), digits.end(),
                       [&](char c) { return IsWildDigit(c, with_x); })
               ? ~uint64_t{0}
               : 0;
  }
  return DigitXzBits(digits, kBits, with_x);
}

// §12.5: the width and signedness every operand of a case statement is
// compared at, the widest of the selector and the item expressions, signed
// only where every one of them is.
struct CaseOperands {
  uint32_t width;
  bool all_signed;
};

uint64_t CaseBits(const ConstVal& v, const CaseOperands& ops) {
  auto bits = static_cast<uint64_t>(v.value);
  if (!ops.all_signed) bits &= WidthMask(v.width);
  return bits & WidthMask(ops.width);
}

// §12.5.4: `[lo:hi]` in a case inside item, a select with no base.
bool IsInsideRange(const Expr* p) {
  return p->kind == ExprKind::kSelect && p->index != nullptr &&
         p->index_end != nullptr;
}

std::array<const Expr*, 2> PatternOperands(const Stmt* s, const Expr* p) {
  if (s->case_inside && IsInsideRange(p)) return {p->index, p->index_end};
  return {p, nullptr};
}

bool SizeCase(const Stmt* s, const ConstVal& sel, const ScopeMap& locals,
              CaseOperands& ops) {
  ops = {sel.width, sel.is_signed};
  for (const CaseItem& ci : s->case_items) {
    for (const Expr* p : ci.patterns) {
      for (const Expr* e : PatternOperands(s, p)) {
        if (e == nullptr) continue;
        auto v = ConstEvalFull(e, locals);
        if (!v) return false;
        ops.width = std::max(ops.width, v->width);
        ops.all_signed = ops.all_signed && v->is_signed;
      }
    }
  }
  return true;
}

std::optional<bool> InsideRangeMatches(const Expr* p, const ConstVal& sel,
                                       const CaseOperands& ops,
                                       const ScopeMap& locals) {
  auto lo = ConstEvalFull(p->index, locals);
  auto hi = ConstEvalFull(p->index_end, locals);
  if (!lo || !hi) return std::nullopt;
  if (ops.all_signed) return lo->value <= sel.value && sel.value <= hi->value;
  uint64_t s = CaseBits(sel, ops);
  return CaseBits(*lo, ops) <= s && s <= CaseBits(*hi, ops);
}

// The x, z and `?` bits of the item `p` that match any selector bit: z and
// `?` for casez (§12.5.1), x as well for casex and for case inside's `==?`
// (§12.5.4, §11.4.6), and none for case.
uint64_t IgnoredBits(const Stmt* s, const Expr* p) {
  if (s->case_inside || s->case_kind == TokenKind::kKwCasex)
    return LiteralXzBits(p, true);
  if (s->case_kind == TokenKind::kKwCasez) return LiteralXzBits(p, false);
  return 0;
}

// Whether the item `p` matches the selector `sel`. A constant selector holds
// no x or z, so an x or z bit of the item the comparison does not ignore
// matches none of it.
std::optional<bool> PatternMatches(const Stmt* s, const Expr* p,
                                   const ConstVal& sel, const CaseOperands& ops,
                                   const ScopeMap& locals) {
  if (s->case_inside && IsInsideRange(p))
    return InsideRangeMatches(p, sel, ops, locals);
  auto v = ConstEvalFull(p, locals);
  if (!v) return std::nullopt;
  // The item's x and z bits are its own, within its width; the bits it is
  // extended by are 0 (§12.5).
  const uint64_t kOwn = WidthMask(v->width);
  const uint64_t kIgnored = IgnoredBits(s, p) & kOwn;
  const uint64_t kMask = WidthMask(ops.width);
  if ((LiteralXzBits(p, true) & kOwn & ~kIgnored) != 0) return false;
  return ((CaseBits(sel, ops) ^ CaseBits(*v, ops)) & ~kIgnored & kMask) == 0;
}

}  // namespace

std::optional<const Stmt*> ConstFuncCaseArm(const Stmt* s,
                                            const ScopeMap& locals) {
  if (s->case_matches) return std::nullopt;
  auto sel = ConstEvalFull(s->condition, locals);
  if (!sel) return std::nullopt;
  CaseOperands ops{};
  if (!SizeCase(s, *sel, locals, ops)) return std::nullopt;
  const Stmt* fallback = nullptr;
  for (const CaseItem& ci : s->case_items) {
    if (ci.is_default) {
      fallback = ci.body;
      continue;
    }
    for (const Expr* p : ci.patterns) {
      auto matched = PatternMatches(s, p, *sel, ops, locals);
      if (!matched) return std::nullopt;
      if (*matched) return ci.body;
    }
  }
  return fallback;
}

}  // namespace delta
