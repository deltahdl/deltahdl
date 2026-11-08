#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/assertion_walk.h"
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

static std::string TypeTableKey(const DataType& type) {
  if (type.scope_name.empty()) return std::string(type.type_name);
  return std::string(type.scope_name) + "::" + std::string(type.type_name);
}

static const DataType* ClassTypedefType(const ClassDecl& decl,
                                        std::string_view name) {
  for (const ClassMember* m : decl.members) {
    if (m->kind != ClassMemberKind::kTypedef || m->name != name) continue;
    return m->typedef_item ? &m->typedef_item->typedef_type : nullptr;
  }
  return nullptr;
}

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

static void CollectChainNames(const Expr* e, std::vector<const Expr*>& names) {
  while (e->kind == ExprKind::kMemberAccess || e->kind == ExprKind::kSelect) {
    if (e->kind == ExprKind::kMemberAccess) {
      e = e->lhs;
      continue;
    }
    CollectBareIdents(e->index, names);
    CollectBareIdents(e->index_end, names);
    e = e->base;
  }
  CollectBareIdents(e, names);
}

static void CollectRunningNames(const Expr* bound,
                                std::vector<const Expr*>& names) {
  CollectBareIdents(bound, names);
  ForEachSubExpr(bound, [&names](const Expr* e) {
    if (e->kind == ExprKind::kMemberAccess) CollectChainNames(e, names);
  });
}

static uint64_t RunningSpan(const Expr* left, const Expr* right,
                            SimContext& ctx) {
  int64_t lv = SelectBoundValue(EvalExpr(left, ctx, ctx.GetArena()));
  int64_t rv = SelectBoundValue(EvalExpr(right, ctx, ctx.GetArena()));
  return static_cast<uint64_t>((lv >= rv ? lv - rv : rv - lv) + 1);
}

static uint32_t RunningPackedDimProduct(const DataType& type, SimContext& ctx) {
  if (!type.packed_dim_left || !type.packed_dim_right) return 0;
  std::vector<std::pair<Expr*, Expr*>> dims{
      {type.packed_dim_left, type.packed_dim_right}};
  dims.insert(dims.end(), type.extra_packed_dims.begin(),
              type.extra_packed_dims.end());
  std::vector<const Expr*> names;
  for (const auto& [left, right] : dims) {
    CollectRunningNames(left, names);
    CollectRunningNames(right, names);
  }
  if (names.empty()) return 0;
  for (const Expr* name : names) {
    if (ctx.FindVariable(name->text) == nullptr) return 0;
  }
  uint64_t product = 1;
  for (const auto& [left, right] : dims)
    product *= RunningSpan(left, right, ctx);
  return static_cast<uint32_t>(product);
}

static uint32_t DeclaredPackedDimProduct(const DataType& type,
                                         SimContext& ctx) {
  uint32_t folded = PackedDimProduct(type);
  return folded != 0 ? folded : RunningPackedDimProduct(type, ctx);
}

static uint32_t RunningMemberWidth(const StructMember& m, SimContext& ctx) {
  if (IsDynamicArrayMember(m)) return kDynamicMemberHandleWidth;
  uint32_t each = EvalStructMemberWidth(m);
  if (m.nested_type != nullptr) {
    each = DeclaredTypeWidth(*m.nested_type, ctx);
  } else if (m.resolved_width == 0 && m.type_kind == DataTypeKind::kNamed) {
    DataType own;
    own.kind = m.type_kind;
    own.type_name = m.type_name;
    own.scope_name = m.scope_name;
    own.packed_dim_left = m.packed_dim_left;
    own.packed_dim_right = m.packed_dim_right;
    own.extra_packed_dims = m.extra_packed_dims;
    each = DeclaredTypeWidth(own, ctx);
  }
  return each * UnpackedMemberCount(m);
}

uint32_t DeclaredTypeWidth(const DataType& type, SimContext& ctx) {
  if (type.kind == DataTypeKind::kStruct || type.kind == DataTypeKind::kUnion) {
    uint32_t each = CombinedMemberWidth(type, [&ctx](const StructMember& m) {
      return RunningMemberWidth(m, ctx);
    });
    uint32_t outer = DeclaredPackedDimProduct(type, ctx);
    return outer > 0 ? each * outer : each;
  }
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
  uint32_t outer = DeclaredPackedDimProduct(type, ctx);
  return outer > 0 ? base * outer : base;
}

bool DeclaredTypeIsSigned(const DataType& type, const SimContext& ctx) {
  if (type.kind == DataTypeKind::kNamed)
    return ctx.FindTypeSigned(TypeTableKey(type));
  return IsSignedType(type, {});
}

DataTypeKind DeclaredTypeKind(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return type.kind;
  return ctx.FindTypeKind(TypeTableKey(type));
}

static bool IsTwoStateIntegerKind(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kByte ||
         kind == DataTypeKind::kShortint || kind == DataTypeKind::kInt ||
         kind == DataTypeKind::kLongint;
}

static bool IsPackedAggregate(const DataType& type) {
  return (type.kind == DataTypeKind::kStruct ||
          type.kind == DataTypeKind::kUnion) &&
         (type.is_packed || type.is_soft);
}

static bool MemberIs4State(const StructMember& m, const SimContext& ctx) {
  if (m.nested_type != nullptr)
    return DeclaredTypeIs4State(*m.nested_type, ctx);
  DataType own;
  own.kind = m.type_kind;
  own.type_name = m.type_name;
  own.scope_name = m.scope_name;
  return DeclaredTypeIs4State(own, ctx);
}

bool DeclaredTypeIs4State(const DataType& type, const SimContext& ctx) {
  if (IsPackedAggregate(type)) {
    return std::any_of(
        type.struct_members.begin(), type.struct_members.end(),
        [&](const StructMember& m) { return MemberIs4State(m, ctx); });
  }
  if (type.kind != DataTypeKind::kNamed) return Is4stateType(type, {});
  std::string key = TypeTableKey(type);
  if (const EnumTypeInfo* e = ctx.FindEnumType(key)) return e->is_4state;
  if (const StructTypeInfo* s = ctx.FindStructType(key);
      s != nullptr && s->is_packed)
    return HasFourStateMember(*s);
  return !IsTwoStateIntegerKind(ctx.FindTypeKind(key));
}

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

static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

bool DeclaredTypeIsReal(const DataType& type, const SimContext& ctx) {
  if (IsRealKind(type.kind)) return true;
  return type.kind == DataTypeKind::kNamed &&
         IsRealKind(ctx.FindTypeKind(TypeTableKey(type)));
}

Logic4Vec ToDeclaredReal(const Logic4Vec& value, const DataType* type,
                         SimContext& ctx, Arena& arena) {
  if (type == nullptr || !DeclaredTypeIsReal(*type, ctx)) return value;
  uint32_t width = DeclaredTypeWidth(*type, ctx) == 32 ? 32 : 64;
  return MakeRealVec(arena, RealValueOf(value), width);
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

static std::vector<uint64_t> DecimalDigitWords(std::string_view digits) {
  std::vector<uint64_t> words{0};
  for (char c : digits) {
    if (c < '0' || c > '9') break;
    MulTenAdd(words, static_cast<uint64_t>(c - '0'));
  }
  return words;
}

static uint32_t WordsBitLength(const std::vector<uint64_t>& words) {
  size_t n = words.size();
  while (n > 0 && words[n - 1] == 0) --n;
  if (n == 0) return 0;
  return static_cast<uint32_t>((n - 1) * 64) +
         static_cast<uint32_t>(std::bit_width(words[n - 1]));
}

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

static uint32_t TopDigitBits(char c, int bpd) {
  int dval = DigitValue(c);
  if (dval < 0) return static_cast<uint32_t>(bpd);
  return static_cast<uint32_t>(std::bit_width(static_cast<unsigned>(dval)));
}

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
  if (uint32_t based = UnsizedBasedLiteralWidth(text); based > 0) return based;
  if (uint32_t wide = WideDecimalLiteralWidth(text); wide > 0) return wide;
  const auto kBits = static_cast<uint32_t>(std::bit_width(val)) +
                     (IsSignedLiteral(text) ? 1U : 0U);
  const uint32_t kWidth = std::max(kBits, uint32_t{32});
  return text.empty() ? std::min(kWidth, uint32_t{64}) : kWidth;
}

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
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
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

static Logic4Vec DecimalLiteralVec(std::string_view digits, uint32_t width,
                                   Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::vector<uint64_t> words = DecimalDigitWords(digits);
  for (uint32_t w = 0; w < vec.nwords && w < words.size(); ++w)
    vec.words[w].aval = words[w] & WordMaskWithinWidth(width, w);
  return vec;
}

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
    if (IsUnsizedLiteral(expr->text) && context_width > width &&
        MsbBvalSet(vec, width)) {
      vec = ParseBasedXZLiteral(expr->text, context_width, arena);
      width = context_width;
    }
    vec.is_signed = is_signed;
    if (IsUnsizedLiteral(expr->text) && MsbBvalSet(vec, width)) {
      vec.is_signed = true;
    }
    return vec;
  }
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
