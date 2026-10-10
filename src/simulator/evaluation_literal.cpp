#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static bool IsXChar(char c) { return c == 'x' || c == 'X'; }
static bool IsZChar(char c) { return c == 'z' || c == 'Z' || c == '?'; }

// The key the type_widths, type_kinds and type_signed tables record a named
// type under. The three are built by PopulateTypeWidths in
// src/elaborator/elaborator.cpp from the elaborator's typedef table, and that
// table enters a package's or a class's typedef under "Scope::name"
// (RegisterScopedTypedef in src/elaborator/elaborator_resolve.cpp), since §26.3
// references a package's declarations through the package name whether or not
// the package was imported, and §8.23 makes a class-scoped name a different
// name from the bare one. A DataType carries the two halves apart, in
// scope_name and type_name, and every reader here asked the tables for the
// type_name alone: `pkg::nib_t v;` declared as a block item found nothing
// under "nib_t", and was created at the 32-bit carrier CreateDeclVariable
// substitutes for a type nothing could size -- v = -1 read 4294967295 and
// $bits(v) 32, where the type §6.18 has that name stand for is four bits wide.
static std::string TypeTableKey(const DataType& type) {
  if (type.scope_name.empty()) return std::string(type.type_name);
  return std::string(type.scope_name) + "::" + std::string(type.type_name);
}

// §8.23: the type a typedef member `name` of the class `decl` declares, or
// null where the class declares no typedef of that name.
static const DataType* ClassTypedefType(const ClassDecl& decl,
                                        std::string_view name) {
  for (const ClassMember* m : decl.members) {
    if (m->kind != ClassMemberKind::kTypedef || m->name != name) continue;
    return m->typedef_item ? &m->typedef_item->typedef_type : nullptr;
  }
  return nullptr;
}

// §8.25: the type the specialization `actuals` binds the type parameter
// `pname` of `decl` to: the actual its `#(...)` list gives, else the default
// the class declares (§8.25.1), else null for a parameter given no default.
static const DataType* SpecializationActual(
    const ClassDecl& decl, const std::vector<DataType>& actuals,
    std::string_view pname) {
  for (size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first != pname) continue;
    if (const DataType* actual = ActualForParam(actuals, i, pname))
      return actual;
    return i < decl.param_types.size() ? &decl.param_types[i] : nullptr;
  }
  return nullptr;
}

// §8.26.3 has a typedef of a parameterized interface class, `typedef T1[1:0]
// T2` in `IntfA #(type T1 = logic)`, named through a specialization as a
// method's return type, `IntfA#(bit[1:0])::T2`; §8.25 binds T1 to the
// specialization's actual throughout the class, so the type is four bits.
// The elaborated table holds `IntfA::T2` sized with T1 unbound, which is no
// width at all. Where the name carries a scope and type actuals and the
// typedef's type names a type parameter of the class, the width is the
// actual's -- by ActualForParam, the one the `#(...)` list gives, else the
// default the class declares (§8.25.1) -- times the typedef's own packed
// dimensions and the use-site ones (§7.4.4). 0 for every other type. Answered
// here, under DeclaredTypeWidth, rather than at the one site that sizes a
// method's result: ExecFunctionBody asks this same question to decide whether
// a `return` is resized to the result variable at all, and with the answer
// given at the sizing site alone the variable was four bits and `return 2;`
// still handed the caller the expression's own 32.
static uint32_t SpecializedTypedefWidth(const DataType& type, SimContext& ctx) {
  if (type.scope_name.empty() || type.type_params.empty()) return 0;
  const ClassTypeInfo* cls = ctx.FindClassType(type.scope_name);
  if (cls == nullptr || cls->decl == nullptr) return 0;
  const ClassDecl& decl = *cls->decl;
  const DataType* alias = ClassTypedefType(decl, type.type_name);
  if (alias == nullptr || alias->kind != DataTypeKind::kNamed) return 0;
  if (decl.type_param_names.count(alias->type_name) == 0) return 0;
  const DataType* actual =
      SpecializationActual(decl, type.type_params, alias->type_name);
  if (actual == nullptr) return 0;
  uint32_t width = DeclaredTypeWidth(*actual, ctx);
  if (uint32_t inner = PackedDimProduct(*alias); inner > 0) width *= inner;
  if (uint32_t outer = PackedDimProduct(type); outer > 0) width *= outer;
  return width;
}

// §8.23: a typedef a class declares, named bare in a method of the class or
// of one extending it, `S v` for the class's `S`, is as wide as the table
// holds it under "C::S". The class itself is its default specialization; a
// specialization's own typedef folds with its values, which that entry does
// not hold, so the walk stops at one. 0 outside a method or where no class of
// the chain declares the name.
//
// §8.25: a class with a value parameter has its aggregate typedef folded with
// the running specialization's values (MethodClassTypedefLayout), whatever
// the specialization.
static uint32_t MethodClassTypedefWidth(std::string_view name,
                                        SimContext& ctx) {
  if (const StructTypeInfo* layout =
          MethodClassTypedefLayout(name, ctx, nullptr)) {
    return layout->total_width;
  }
  for (const ClassTypeInfo* c = ctx.CurrentMethodClass(); c != nullptr;
       c = c->parent) {
    if (c->param_actuals != nullptr) return 0;
    if (uint32_t width =
            ctx.FindTypeWidth(std::string(c->name) + "::" + std::string(name)))
      return width;
  }
  return 0;
}

// §7.4.1 with §6.20.2: a packed dimension's bounds are constant expressions,
// and a value parameter's name is one. EvalTypeWidth folds a bound with no
// scope, so a range naming a parameter does not fold there, and a variable
// declared while the design runs -- in a named block, a subroutine body or a
// for-loop initialization -- fell to the width of its base type, one bit for
// `logic [W-1:0]`. The simulator holds each parameter as a variable of the
// instance declaring it, so each name a bound reads is looked up in the
// running scope and the range folded against those values, which gives every
// instance its own width. 0 where a name resolves to no variable or to an
// unknown value, which leaves the fold without a scope in charge.
static uint32_t RunningPackedDimProduct(const DataType& type, SimContext& ctx) {
  if (!type.packed_dim_left || !type.packed_dim_right) return 0;
  std::vector<const Expr*> names;
  CollectBareIdents(type.packed_dim_left, names);
  CollectBareIdents(type.packed_dim_right, names);
  for (const auto& [left, right] : type.extra_packed_dims) {
    CollectBareIdents(left, names);
    CollectBareIdents(right, names);
  }
  if (names.empty()) return 0;
  ScopeMap scope;
  for (const Expr* name : names) {
    const Variable* var = ctx.FindVariable(name->text);
    if (var == nullptr || !var->value.IsKnown()) return 0;
    scope[name->text] = SelectBoundValue(var->value);
  }
  return PackedDimProduct(type, scope);
}

// The element count of the packed dimensions `type` writes, folded without a
// scope where that is enough and against the running one otherwise.
static uint32_t DeclaredPackedDimProduct(const DataType& type,
                                         SimContext& ctx) {
  uint32_t folded = PackedDimProduct(type);
  return folded != 0 ? folded : RunningPackedDimProduct(type, ctx);
}

uint32_t DeclaredTypeWidth(const DataType& type, SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed && PackedDimProduct(type) == 0) {
    if (uint32_t running = RunningPackedDimProduct(type, ctx)) return running;
  }
  uint32_t width = EvalTypeWidth(type);
  if (width != 0) return width;
  if (type.kind != DataTypeKind::kNamed) return 0;
  uint32_t base = ctx.FindTypeWidth(TypeTableKey(type));
  if (base == 0 && type.scope_name.empty())
    base = MethodClassTypedefWidth(type.type_name, ctx);
  if (base == 0) return SpecializedTypedefWidth(type, ctx);
  // §7.4.4: packed dimensions may also be built up in stages through a
  // typedef, and a dimension written where the name is used stacks on the ones
  // the typedef itself carries -- `bsix [1:10] v5` on a `typedef bit [1:5]
  // bsix` is 50 bits. The table holds what the name stands for; the use-site
  // range is how many of those the declaration asks for.
  uint32_t outer = DeclaredPackedDimProduct(type, ctx);
  return outer > 0 ? base * outer : base;
}

// §6.18: an object declared with a type name has the type the name stands for,
// so a variable declared with a typedef of `string` is a string, and §6.16
// gives one no declared width and the initial value "". Every declaration path
// recognised a string by DataType::kind alone, which is kNamed for such a name,
// so the declaration fell to the 32-bit carrier substituted for a type nothing
// could size and was never registered as a string: %s, the string methods and a
// string comparison all read it as a bit vector. The resolved kind the
// elaborator records beside the width is what answers it.
// §6.11.1/§6.18: whether the declared type is signed, whether written with the
// `signed` keyword, defaulted by one of the signed integer types, or reached
// through a typedef name. The simulator carries no TypedefMap, so every site
// asked IsSignedType with an empty one and a formal or local written with a
// name for a signed type was created unsigned: -1 read back as 255, and every
// relational and arithmetic operator on it read a magnitude. #3475 had already
// moved such a declaration's width onto the elaborated table, so the two
// disagreed about where the type came from until this followed it.
bool DeclaredTypeIsSigned(const DataType& type, const SimContext& ctx) {
  if (type.kind == DataTypeKind::kNamed)
    return ctx.FindTypeSigned(TypeTableKey(type));
  return IsSignedType(type, {});
}

DataTypeKind DeclaredTypeKind(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return type.kind;
  return ctx.FindTypeKind(TypeTableKey(type));
}

// §6.11.2's 2-state integer types, the kinds of value that hold no x or z.
static bool IsTwoStateIntegerKind(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kByte ||
         kind == DataTypeKind::kShortint || kind == DataTypeKind::kInt ||
         kind == DataTypeKind::kLongint;
}

// §6.18: a name is known to stand for a 2-state type where the design
// registered it as an enumeration with a 2-state base (§6.19), a packed
// structure or union with no 4-state member (§7.2.1, §7.3.1), or a kind among
// §6.11.2's 2-state integer types. Any other name -- one the tables do not
// hold, or one standing for a class, a string or an unpacked aggregate --
// answers 4-state: keeping a bit §6.11.2 would have cleared is the smaller
// error than clearing one it would have kept.
bool DeclaredTypeIs4State(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return Is4stateType(type.kind);
  std::string key = TypeTableKey(type);
  if (const EnumTypeInfo* e = ctx.FindEnumType(key)) return e->is_4state;
  if (const StructTypeInfo* s = ctx.FindStructType(key);
      s != nullptr && s->is_packed)
    return HasFourStateMember(*s);
  return !IsTwoStateIntegerKind(ctx.FindTypeKind(key));
}

// §11.5.1 with §6.18: the packed range the declared type was written with,
// for a type reached through a name. The name is looked up under the same key
// the width is, so a class-scoped `Node::value_t` (§8.23) finds the entry
// RegisterClassTypedefs recorded for it. A name written with a packed dimension
// of its own stacks that dimension on the type (§7.4.4) and is left to
// RecordPackedRange, which reads the dimension off the declaration itself.
static std::optional<PackedRange> DeclaredTypeRange(const DataType& type,
                                                    const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || type.packed_dim_left != nullptr)
    return std::nullopt;
  return ctx.FindTypeRange(TypeTableKey(type));
}

void RecordDeclaredRange(const DataType& type, Variable* v, SimContext& ctx,
                         Arena& arena) {
  RecordPackedRange(&type, v, ctx, arena);
  if (v->has_packed_range) return;
  auto range = DeclaredTypeRange(type, ctx);
  if (!range) return;
  // The range names the bits of the type it was recorded for, and the variable
  // was sized from the same type; storage of another width -- the carrier a
  // declaration nothing could size is created at, or a string's -- is not that
  // vector and stays addressed as [width-1:0], as RecordPackedRange leaves a
  // declaration whose bounds it cannot fold.
  auto span = static_cast<uint64_t>(range->HighIndex() - range->LowIndex() + 1);
  if (span != v->value.width) return;
  v->packed_range = *range;
  v->has_packed_range = true;
}

bool DeclaredTypeIsString(const DataType& type, const SimContext& ctx) {
  if (type.kind == DataTypeKind::kString) return true;
  return type.kind == DataTypeKind::kNamed &&
         ctx.FindTypeKind(TypeTableKey(type)) == DataTypeKind::kString;
}

// §6.12: the three kinds the clause declares real variables by. A typedef
// name is asked the same way a string's is, by the kind the elaborator
// recorded for it.
static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

bool DeclaredTypeIsReal(const DataType& type, const SimContext& ctx) {
  if (IsRealKind(type.kind)) return true;
  return type.kind == DataTypeKind::kNamed &&
         IsRealKind(ctx.FindTypeKind(TypeTableKey(type)));
}

static int BitsPerDigit(char base_letter) {
  switch (base_letter) {
    case 'h':
    case 'H':
      return 4;
    case 'o':
    case 'O':
      return 3;
    case 'b':
    case 'B':
      return 1;
    default:
      return 0;
  }
}

static int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static size_t ParseLiteralBase(std::string_view text, std::string& buf,
                               int& bpd) {
  buf = LiteralTextWithoutSeparators(text);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) return 0;
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  bpd = (i < buf.size()) ? BitsPerDigit(buf[i]) : 0;
  return i;
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

// §5.7.1: the value the decimal `digits` form, as 64-bit words least
// significant first, however many words the value needs. The digits are the
// literal's third token with the `_` separators already dropped, so the fold
// ends at the first character that is no decimal digit.
static std::vector<uint64_t> DecimalDigitWords(std::string_view digits) {
  std::vector<uint64_t> words{0};
  for (char c : digits) {
    if (c < '0' || c > '9') break;
    MulTenAdd(words, static_cast<uint64_t>(c - '0'));
  }
  return words;
}

// The number of bits the magnitude `words` holds needs: the position of its
// highest set bit plus one, or 0 for a zero value.
static uint32_t WordsBitLength(const std::vector<uint64_t>& words) {
  size_t n = words.size();
  while (n > 0 && words[n - 1] == 0) --n;
  if (n == 0) return 0;
  return static_cast<uint32_t>((n - 1) * 64) +
         static_cast<uint32_t>(std::bit_width(words[n - 1]));
}

// §5.7.1: the width of an unsized decimal literal whose value needs more than
// 64 bits -- the value's bit length, plus the sign bit a signed number keeps
// -- or 0 for any other literal. `2^70` written as a simple decimal is 72
// bits, `'d` before the same digits 71. Expr::int_val holds the value's low
// 64 bits alone, so the digits are what say whether there is more: a literal
// whose text has fewer than 20 characters has at most 19 digits and is below
// 10^19 < 2^64, and is answered without reading them.
static uint32_t WideDecimalLiteralWidth(std::string_view text) {
  if (text.size() < 20) return 0;
  std::string buf;
  int bpd = 0;
  size_t i = ParseLiteralBase(text, buf, bpd);
  if (bpd != 0) return 0;
  if (i != 0) ++i;
  uint32_t len =
      WordsBitLength(DecimalDigitWords(std::string_view(buf).substr(i)));
  if (len <= 64) return 0;
  return IsSignedLiteral(text) ? len + 1 : len;
}

// §5.7.1: the bits the one hex, octal or binary digit `c` needs at the top of
// a number: those of its value, so a leading 7 needs 3 and a leading 0 none,
// or the base's full `bpd` for an x, z or ? digit, which sets all of them.
static uint32_t TopDigitBits(char c, int bpd) {
  int dval = DigitValue(c);
  if (dval < 0) return static_cast<uint32_t>(bpd);
  return static_cast<uint32_t>(std::bit_width(static_cast<unsigned>(dval)));
}

// §5.7.1: the width of an unsized hex, octal or binary literal -- the bits
// its digits need once the leading zeros are dropped, an x, z or ? digit
// counted at its base's full width, plus the sign bit a signed number keeps
// -- at least 32, so `'h7_0000_0000` is 35 bits, `'sh8000_0000` 33 and
// `'hF_FFFF_FFFF_FFFF_FFFF` 68. Returns 0 for a sized or a decimal literal.
// Expr::int_val holds the value's low 64 bits alone, so the digits are what
// say how wide the value is.
static uint32_t UnsizedBasedLiteralWidth(std::string_view text) {
  if (text.size() < 2 || text.front() != '\'') return 0;
  size_t i = 1;
  if (text[i] == 's' || text[i] == 'S') ++i;
  int bpd = (i < text.size()) ? BitsPerDigit(text[i]) : 0;
  if (bpd == 0) return 0;
  uint32_t len = 0;
  for (char c : LiteralTextWithoutSeparators(text.substr(i + 1))) {
    len = (len == 0) ? TopDigitBits(c, bpd) : len + static_cast<uint32_t>(bpd);
  }
  if (IsSignedLiteral(text)) ++len;
  return std::max(len, uint32_t{32});
}

uint32_t LiteralWidth(std::string_view text, uint64_t val) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      if (text[i] >= '0' && text[i] <= '9') w = w * 10 + (text[i] - '0');
    }
    if (w > 0) return w;
  }
  // An unsized number is at least 32 bits, widened to the minimum width that
  // holds its value. §5.7.1 additionally requires a signed unsized number to
  // keep a sign bit, so a value whose most significant magnitude bit would
  // land on the sign position needs one extra bit to stay non-negative. A
  // based number is sized from its digits, and a decimal value past 64 bits
  // likewise, `val` being the value's low 64 bits alone.
  if (uint32_t based = UnsizedBasedLiteralWidth(text); based > 0) return based;
  if (uint32_t wide = WideDecimalLiteralWidth(text); wide > 0) return wide;
  // Up to 64 bits `val` is the whole value: its bit length, plus the sign bit,
  // so 2^32 is 34 bits as a simple decimal and 2^63 is 65.
  const auto kBits = static_cast<uint32_t>(std::bit_width(val)) +
                     (IsSignedLiteral(text) ? 1U : 0U);
  const uint32_t kWidth = std::max(kBits, uint32_t{32});
  // A literal the elaborator builds, such as an enumeration member's value,
  // has no text and holds its value in `val` alone, a negative one as its
  // 64-bit two's complement, so it is never wider than those 64 bits.
  return text.empty() ? std::min(kWidth, uint32_t{64}) : kWidth;
}

// §5.7.1 (printed page 78): an unbased unsized literal is one bit wide where
// it is self-determined -- `$bits('1)` is 1, `'1` prints 1 and `'1 == 1'b1`
// holds -- and sets every bit of the context it stands in: EvalExpr fills it
// to the width a context hands down, and Logic4Vec::fills_width has a later
// resize replicate the bit where the width is settled only by the
// assignment, the formal or the operand the value reaches. Carried at 64
// bits, the literal answered 64 to $bits and 18446744073709551615 to %0d.
Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena) {
  auto text = expr->text;
  auto vec = MakeLogic4Vec(arena, 1);
  vec.fills_width = true;
  if (text.size() >= 2 && text[0] == '\'') {
    char c = text[1];
    if (c == '1') vec.words[0] = {1, 0};
    if (c == 'x' || c == 'X') vec.words[0] = {1, 1};
    if (c == 'z' || c == 'Z' || c == '?') vec.words[0] = {0, 1};
    return vec;
  }
  vec.words[0] = {expr->int_val & 1, 0};
  return vec;
}
static bool TextHasXZ(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i)
    if (IsXChar(text[i]) || IsZChar(text[i])) return true;
  return false;
}

static void SetDigitBits(Logic4Vec& vec, uint32_t& bit_pos, int bit_count,
                         char digit, uint32_t width) {
  bool is_x = IsXChar(digit);
  bool is_z = IsZChar(digit);
  int dval = DigitValue(digit);
  for (int b = 0; b < bit_count && bit_pos < width; ++b, ++bit_pos) {
    uint32_t word = bit_pos / 64;
    uint64_t mask = uint64_t{1} << (bit_pos % 64);
    if (is_x) {
      // An x literal digit uses the (aval=1, bval=1) encoding.
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
      // A z literal digit uses the (aval=0, bval=1) encoding, matching FillXZ
      // and the raw-bit consumers (see net.cpp GetBitVal).
      vec.words[word].bval |= mask;
    } else if (dval >= 0 && (dval & (1 << b))) {
      vec.words[word].aval |= mask;
    }
  }
}
static void FillXZ(Logic4Vec& vec, uint32_t start, uint32_t end, bool is_x) {
  for (uint32_t b = start; b < end; ++b) {
    uint32_t word = b / 64;
    uint64_t mask = uint64_t{1} << (b % 64);
    if (is_x) vec.words[word].aval |= mask;
    vec.words[word].bval |= mask;
  }
}
static Logic4Vec ParseBasedXZLiteral(std::string_view text, uint32_t width,
                                     Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::string buf;
  int bpd = 0;
  size_t i = ParseLiteralBase(text, buf, bpd);
  if (i == 0) return vec;
  if (bpd == 0) {
    ++i;
    char first = (i < buf.size()) ? buf[i] : '\0';
    if (IsXChar(first) || IsZChar(first)) FillXZ(vec, 0, width, IsXChar(first));
    return vec;
  }
  ++i;
  uint32_t bit_pos = 0;
  for (auto j = buf.size(); j > i && bit_pos < width; --j)
    SetDigitBits(vec, bit_pos, bpd, buf[j - 1], width);

  if (bit_pos < width && i < buf.size()) {
    char lm = buf[i];
    if (IsXChar(lm) || IsZChar(lm)) FillXZ(vec, bit_pos, width, IsXChar(lm));
  }
  return vec;
}

// §5.7.1: the value the decimal `digits` form, laid into a vector of `width`
// bits. A value wider than the size constant is truncated from the left, so
// each word is masked to the bits within the width, and a narrower one is
// padded with the zeros the fresh vector holds.
static Logic4Vec DecimalLiteralVec(std::string_view digits, uint32_t width,
                                   Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::vector<uint64_t> words = DecimalDigitWords(digits);
  for (uint32_t w = 0; w < vec.nwords && w < words.size(); ++w)
    vec.words[w].aval = words[w] & WordMaskWithinWidth(width, w);
  return vec;
}

// The whole value of a literal wider than 64 bits, read from its digits again
// rather than from the 64 bits Expr::int_val holds:
// `80'd1208925819614629174706177` (2^80 + 1) sets bit 80 as well as bit 0.
static Logic4Vec EvalWideLiteral(std::string_view text, uint32_t width,
                                 Arena& arena) {
  std::string buf;
  int bpd = 0;
  size_t i = ParseLiteralBase(text, buf, bpd);
  if (bpd != 0) return ParseBasedXZLiteral(text, width, arena);
  if (i != 0) ++i;
  return DecimalLiteralVec(std::string_view(buf).substr(i), width, arena);
}

static bool IsUnsizedLiteral(std::string_view text) {
  return !text.empty() && text.front() == '\'';
}

static bool MsbBvalSet(const Logic4Vec& vec, uint32_t width) {
  if (width == 0 || vec.nwords == 0) return false;
  uint32_t msb_word = (width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((width - 1) % 64);
  return (vec.words[msb_word].bval & msb_mask) != 0;
}

Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena,
                         uint32_t context_width) {
  uint32_t width = LiteralWidth(expr->text, expr->int_val);
  bool is_signed = IsSignedLiteral(expr->text);
  if (TextHasXZ(expr->text)) {
    auto vec = ParseBasedXZLiteral(expr->text, width, arena);
    // §5.7.1: an unsized literal whose high-order bit is x or z extends with it
    // to the width of the expression holding it, an operator's operands
    // included, which ParseBasedXZLiteral's left padding gives.
    if (IsUnsizedLiteral(expr->text) && context_width > width &&
        MsbBvalSet(vec, width)) {
      vec = ParseBasedXZLiteral(expr->text, context_width, arena);
      width = context_width;
    }
    vec.is_signed = is_signed;
    // An unsized literal whose high-order bit ended up as x or z must
    // propagate that high-order bit through any wider context the
    // value is used in. ResizeToWidth performs MSB-pattern extension
    // when is_signed is set, so we piggy-back on that mechanism here
    // without claiming the literal is signed for arithmetic — x/z
    // contaminate any operation regardless of signedness.
    if (IsUnsizedLiteral(expr->text) && MsbBvalSet(vec, width)) {
      vec.is_signed = true;
    }
    return vec;
  }
  // §5.7.1: a literal's value is formed from all its digits at the width the
  // size constant states, or at the width the value needs when unsized. The
  // parser's ParseIntText folds the digits into the 64 bits expr->int_val
  // holds, so a literal up to 64 bits wide is carried whole and int_val is its
  // low 64 bits beyond that; a wider literal is rebuilt from the digit string
  // into a multi-word vector, a based hex, octal or binary one digit by digit
  // through ParseBasedXZLiteral, which reads plain digits as well as x and z
  // (none present here), and a decimal one by the multiply-and-add of
  // DecimalLiteralVec.
  if (width > 64) {
    auto vec = EvalWideLiteral(expr->text, width, arena);
    vec.is_signed = is_signed;
    return vec;
  }
  auto vec = MakeLogic4VecVal(arena, width, expr->int_val);
  vec.is_signed = is_signed;
  return vec;
}

static int HexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static uint8_t SimpleEscapeChar(char c) {
  switch (c) {
    case 'n':
      return '\n';
    case 't':
      return '\t';
    case '\\':
      return '\\';
    case '"':
      return '"';
    case 'v':
      return '\v';
    case 'f':
      return '\f';
    case 'a':
      return '\a';
    default:
      return 0;
  }
}

// A.8.8: the `\x one_to_two_digit_hex_number` alternative needs at least one
// hex digit after the x. Answers -1 when none follows, leaving the sequence to
// the `\any_ASCII_character` alternative rather than reading it as \x00.
static int ParseHexEscape(std::string_view text, size_t& i) {
  int val = -1;
  for (int j = 0; j < 2 && i + 1 < text.size(); ++j) {
    int d = HexDigitVal(text[i + 1]);
    if (d < 0) break;
    val = (val < 0 ? 0 : val) * 16 + d;
    ++i;
  }
  return val;
}

static uint8_t ParseOctalEscape(char c, std::string_view text, size_t& i) {
  auto val = static_cast<uint8_t>(c - '0');
  for (int j = 0;
       j < 2 && i + 1 < text.size() && text[i + 1] >= '0' && text[i + 1] <= '7';
       ++j)
    val = val * 8 + static_cast<uint8_t>(text[++i] - '0');
  return val;
}

// The byte a string_escape_seq beginning `\c` stands for, or -1 when it stands
// for no byte at all -- a backslash before a newline is a line continuation.
// A.8.8 lists `\any_ASCII_character` as an alternative in its own right, so
// every sequence the octal and hex alternatives do not match falls to it and
// spells the character itself. That is why an x with no hex digit after it is
// an ordinary x.
static int EscapeByte(char c, std::string_view text, size_t& i) {
  if (uint8_t esc = SimpleEscapeChar(c); esc != 0) return esc;
  if (c == 'x') {
    int hex = ParseHexEscape(text, i);
    return hex >= 0 ? hex : 'x';
  }
  if (c >= '0' && c <= '7') return ParseOctalEscape(c, text, i);
  if (c == '\n') return -1;
  return static_cast<unsigned char>(c);
}

static std::vector<uint8_t> DecodeStringBody(std::string_view text) {
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] != '\\' || i + 1 >= text.size()) {
      bytes.push_back(static_cast<uint8_t>(text[i]));
      continue;
    }
    ++i;
    int b = EscapeByte(text[i], text, i);
    if (b >= 0) bytes.push_back(static_cast<uint8_t>(b));
  }
  return bytes;
}
std::string_view StringLiteralBody(std::string_view text) {
  // §5.9 (printed page 81): a triple-quoted string literal is the text between
  // its `"""` delimiters, and in every other way the same literal as a quoted
  // one; a lone `"` inside it is one of its items.
  if (text.size() >= 6 && text.substr(0, 3) == "\"\"\"")
    return text.substr(3, text.size() - 6);
  if (text.size() >= 2 && text.front() == '"')
    return text.substr(1, text.size() - 2);
  return text;
}

Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena) {
  auto bytes = DecodeStringBody(StringLiteralBody(expr->text));
  uint32_t width = static_cast<uint32_t>(bytes.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < bytes.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(bytes.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(bytes[i]) << bit;
  }
  return vec;
}

}  // namespace delta
