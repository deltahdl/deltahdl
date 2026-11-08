#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

uint64_t WidthMask(uint32_t width) {
  return width >= 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
}

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

struct LiteralDigits {
  uint64_t value = 0;
  uint64_t x = 0;
  uint64_t z = 0;
};

bool IsXDigit(char c) { return c == 'x' || c == 'X'; }
bool IsZDigit(char c) { return c == '?' || c == 'z' || c == 'Z'; }

unsigned DigitValue(char c) {
  if (std::isdigit(static_cast<unsigned char>(c)) != 0)
    return static_cast<unsigned>(c - '0');
  return static_cast<unsigned>(std::tolower(static_cast<unsigned char>(c)) -
                               'a' + 10);
}

void AddDigit(char c, unsigned bits, unsigned shift, LiteralDigits& out) {
  const uint64_t kField = ((uint64_t{1} << bits) - 1) << shift;
  if (IsXDigit(c)) {
    out.x |= kField;
  } else if (IsZDigit(c)) {
    out.z |= kField;
  } else {
    out.value |= (uint64_t{DigitValue(c)} << shift) & kField;
  }
}

LiteralDigits BasedDigits(std::string_view digits, unsigned bits) {
  LiteralDigits out;
  unsigned shift = 0;
  char leftmost = '0';
  for (auto it = digits.rbegin(); it != digits.rend() && shift < 64; ++it) {
    if (*it == '_') continue;
    AddDigit(*it, bits, shift, out);
    leftmost = *it;
    shift += bits;
  }
  if (shift >= 64) return out;
  const uint64_t kAbove = ~uint64_t{0} << shift;
  if (IsXDigit(leftmost)) out.x |= kAbove;
  if (IsZDigit(leftmost)) out.z |= kAbove;
  return out;
}

LiteralDigits DecimalDigits(std::string_view digits) {
  LiteralDigits out;
  if (std::any_of(digits.begin(), digits.end(), IsXDigit)) out.x = ~uint64_t{0};
  if (std::any_of(digits.begin(), digits.end(), IsZDigit)) out.z = ~uint64_t{0};
  return out;
}

std::optional<LiteralDigits> UnknownLiteral(const Expr* e) {
  if (e->kind != ExprKind::kIntegerLiteral) return std::nullopt;
  std::string_view t = e->text;
  size_t pos = t.find('\'');
  if (pos == std::string_view::npos) return std::nullopt;
  ++pos;
  if (pos < t.size() && (t[pos] == 's' || t[pos] == 'S')) ++pos;
  if (pos >= t.size()) return std::nullopt;
  const unsigned kBits = BitsPerDigit(t[pos++]);
  std::string_view digits = t.substr(pos);
  LiteralDigits out =
      kBits == 0 ? DecimalDigits(digits) : BasedDigits(digits, kBits);
  if ((out.x | out.z) == 0) return std::nullopt;
  return out;
}

struct CaseOperands {
  uint32_t width;
  bool all_signed;
};

uint64_t CaseBits(const ConstVal& v, const CaseOperands& ops) {
  auto bits = static_cast<uint64_t>(v.value);
  if (!ops.all_signed) bits &= WidthMask(v.width);
  return bits & WidthMask(ops.width);
}

struct CaseItemValue {
  const Stmt* body = nullptr;
  ConstVal value{0, 32, true};
  std::optional<ConstVal> hi;
  uint64_t x = 0;
  uint64_t z = 0;
};

struct CaseFold {
  CaseOperands ops;
  std::vector<CaseItemValue> items;
  const Stmt* fallback = nullptr;
};

std::optional<ConstVal> FoldOperand(const Expr* e, const ScopeMap& locals,
                                    CaseOperands& ops) {
  auto v = ConstEvalFull(e, locals);
  if (!v) return std::nullopt;
  ops.width = std::max(ops.width, v->width);
  ops.all_signed = ops.all_signed && v->is_signed;
  return v;
}

bool IsInsideRange(const Stmt* s, const Expr* p) {
  return s->case_inside && p->kind == ExprKind::kSelect &&
         p->index_end != nullptr;
}

bool FoldItem(const Stmt* s, const Expr* p, const ScopeMap& locals,
              CaseItemValue& item, CaseOperands& ops) {
  if (IsInsideRange(s, p)) {
    auto lo = FoldOperand(p->index, locals, ops);
    item.hi = FoldOperand(p->index_end, locals, ops);
    if (!lo || !item.hi) return false;
    item.value = *lo;
    return true;
  }
  auto v = FoldOperand(p, locals, ops);
  if (!v) return false;
  item.value = *v;
  if (auto lit = UnknownLiteral(p)) {
    const uint64_t kOwn = WidthMask(v->width);
    item.value.value = static_cast<int64_t>(lit->value & kOwn);
    item.x = lit->x & kOwn;
    item.z = lit->z & kOwn;
  }
  return true;
}

bool FoldCase(const Stmt* s, const ScopeMap& locals, CaseFold& fold) {
  for (const CaseItem& ci : s->case_items) {
    if (ci.is_default) fold.fallback = ci.body;
    for (const Expr* p : ci.patterns) {
      CaseItemValue item;
      item.body = ci.body;
      if (!FoldItem(s, p, locals, item, fold.ops)) return false;
      fold.items.push_back(item);
    }
  }
  return true;
}

uint64_t IgnoredBits(const Stmt* s, const CaseItemValue& item) {
  if (s->case_inside || s->case_kind == TokenKind::kKwCasex)
    return item.x | item.z;
  if (s->case_kind == TokenKind::kKwCasez) return item.z;
  return 0;
}

bool ItemMatches(const Stmt* s, const CaseItemValue& item, const ConstVal& sel,
                 const CaseOperands& ops) {
  if (item.hi) {
    if (ops.all_signed)
      return item.value.value <= sel.value && sel.value <= item.hi->value;
    uint64_t bits = CaseBits(sel, ops);
    return CaseBits(item.value, ops) <= bits && bits <= CaseBits(*item.hi, ops);
  }
  const uint64_t kIgnored = IgnoredBits(s, item);
  if (((item.x | item.z) & ~kIgnored) != 0) return false;
  return ((CaseBits(sel, ops) ^ CaseBits(item.value, ops)) & ~kIgnored &
          WidthMask(ops.width)) == 0;
}

}  // namespace

std::optional<const Stmt*> ConstFuncCaseArm(const Stmt* s,
                                            const ScopeMap& locals) {
  auto sel = ConstEvalFull(s->condition, locals);
  if (!sel) return std::nullopt;
  CaseFold fold{{sel->width, sel->is_signed}, {}, nullptr};
  if (!FoldCase(s, locals, fold)) return std::nullopt;
  for (const CaseItemValue& item : fold.items) {
    if (ItemMatches(s, item, *sel, fold.ops)) return item.body;
  }
  return fold.fallback;
}

}  // namespace delta
