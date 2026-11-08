#include "simulator/eval_string.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/string_methods.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

static uint8_t ByteAtChar(const Logic4Vec& packed, uint32_t i) {
  uint32_t nbytes = packed.width / 8;
  if (i >= nbytes) return 0;
  uint32_t byte_idx = nbytes - 1 - i;
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  if (word >= packed.nwords) return 0;
  return static_cast<uint8_t>((packed.words[word].aval >> bit) & 0xFF);
}

static Logic4Vec PackBytes(const std::vector<uint8_t>& bytes, Arena& arena) {
  uint32_t width = static_cast<uint32_t>(bytes.size()) * 8;
  if (width == 0) width = 8;
  auto out = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < bytes.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(bytes.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    out.words[word].aval |= static_cast<uint64_t>(bytes[i]) << bit;
  }
  return out;
}

Logic4Vec StripStringZeros(const Logic4Vec& packed, Arena& arena) {
  uint32_t nbytes = packed.width / 8;
  std::vector<uint8_t> kept;
  kept.reserve(nbytes);
  for (uint32_t i = 0; i < nbytes; ++i) {
    uint8_t b = ByteAtChar(packed, i);
    if (b != 0) kept.push_back(b);
  }
  return PackBytes(kept, arena);
}

void StringWriteByte(Variable* var, uint32_t idx, uint8_t byte_val,
                     Arena& arena) {
  if (!var) return;
  if (byte_val == 0) return;
  uint32_t nbytes = var->value.width / 8;
  if (idx >= nbytes) return;
  std::vector<uint8_t> bytes;
  bytes.reserve(nbytes);
  for (uint32_t i = 0; i < nbytes; ++i)
    bytes.push_back(ByteAtChar(var->value, i));
  bytes[idx] = byte_val;
  var->value = PackBytes(bytes, arena);
}

std::string Logic4VecToString(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string result;
  result.reserve(nbytes);
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str) {
  uint32_t width = static_cast<uint32_t>(str.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < str.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(str[i])) << bit;
  }
  return vec;
}

struct StringMethodArgs {
  Variable* var;
  const FieldTarget* target;
  std::string str;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
  const Expr* element = nullptr;
};

static void StoreString(const StringMethodArgs& a, std::string_view text) {
  if (a.var != nullptr) {
    a.var->value = StringToLogic4Vec(a.arena, text);
    return;
  }
  if (a.element != nullptr) {
    PerformBlockingAssign(a.element, StringToLogic4Vec(a.arena, text), a.ctx,
                          a.arena);
    return;
  }
  WriteResolvedField(*a.target, StringToLogic4Vec(a.arena, text), a.ctx,
                     a.arena);
}

static Logic4Vec StringLen(const std::string& str, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, str.size());
}

static void StringPutc(const StringMethodArgs& a) {
  if (a.call_expr->args.size() < 2) return;
  auto idx = EvalExpr(a.call_expr->args[0], a.ctx, a.arena).ToUint64();
  auto ch = EvalExpr(a.call_expr->args[1], a.ctx, a.arena).ToUint64();
  if ((ch & 0xFF) == 0) return;
  std::string copy = a.str;
  if (idx < copy.size()) {
    copy[idx] = static_cast<char>(ch & 0xFF);
    StoreString(a, copy);
  }
}

static Logic4Vec StringGetc(const std::string& str, const Expr* call_expr,
                            SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 8, 0);
  auto idx = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  if (idx >= str.size()) return MakeLogic4VecVal(arena, 8, 0);
  return MakeLogic4VecVal(arena, 8, static_cast<unsigned char>(str[idx]));
}

static Logic4Vec StringResult(std::string_view str, Arena& arena) {
  Logic4Vec out = StringToLogic4Vec(arena, str);
  out.is_string = true;
  return out;
}

static Logic4Vec StringToupper(const std::string& str, Arena& arena) {
  std::string upper = str;
  for (auto& c : upper) c = static_cast<char>(std::toupper(c));
  return StringResult(upper, arena);
}

static Logic4Vec StringTolower(const std::string& str, Arena& arena) {
  std::string lower = str;
  for (auto& c : lower) c = static_cast<char>(std::tolower(c));
  return StringResult(lower, arena);
}

static std::string EvalArgAsString(const Expr* arg, SimContext& ctx,
                                   Arena& arena) {
  auto val = EvalExpr(arg, ctx, arena);
  return Logic4VecToString(val);
}

static Logic4Vec CompareResult(int cmp, Arena& arena) {
  Logic4Vec out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
  out.is_signed = true;
  return out;
}

static Logic4Vec StringCompare(const std::string& str, const Expr* call_expr,
                               SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return CompareResult(0, arena);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  return CompareResult(str.compare(other), arena);
}

static Logic4Vec StringIcompare(const std::string& str, const Expr* call_expr,
                                SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return CompareResult(0, arena);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  std::string a = str;
  std::string b = other;
  for (auto& c : a) c = static_cast<char>(std::tolower(c));
  for (auto& c : b) c = static_cast<char>(std::tolower(c));
  return CompareResult(a.compare(b), arena);
}

static Logic4Vec StringSubstr(const std::string& str, const Expr* call_expr,
                              SimContext& ctx, Arena& arena) {
  if (call_expr->args.size() < 2) return StringResult("", arena);
  auto i = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  auto j = EvalExpr(call_expr->args[1], ctx, arena).ToUint64();
  if (i >= str.size() || j >= str.size() || i > j) {
    return StringResult("", arena);
  }
  return StringResult(str.substr(i, j - i + 1), arena);
}

static int DigitValueForBase(char c, int base) {
  if ((base == 10 || base == 16) && c >= '0' && c <= '9') return c - '0';
  if (base == 16 && c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (base == 16 && c >= 'A' && c <= 'F') return c - 'A' + 10;
  if (base == 8 && c >= '0' && c <= '7') return c - '0';
  if (base == 2 && (c == '0' || c == '1')) return c - '0';
  return -1;
}

static Logic4Vec StringAtoBase(const std::string& str, int base, Arena& arena) {
  uint64_t val = 0;
  bool found_digit = false;
  for (char c : str) {
    if (c == '_') continue;
    int digit = DigitValueForBase(c, base);
    if (digit < 0) break;
    val = val * static_cast<uint64_t>(base) + static_cast<uint64_t>(digit);
    found_digit = true;
  }
  if (!found_digit) val = 0;
  return MakeLogic4VecVal(arena, 32, val);
}

static Logic4Vec StringAtoreal(const std::string& str, Arena& arena) {
  std::string cleaned;
  cleaned.reserve(str.size());
  for (size_t i = 0; i < str.size(); ++i) {
    char c = str[i];
    if (c == '_' && !cleaned.empty() &&
        std::isdigit(static_cast<unsigned char>(cleaned.back())) &&
        i + 1 < str.size() &&
        std::isdigit(static_cast<unsigned char>(str[i + 1]))) {
      continue;
    }
    cleaned.push_back(c);
  }
  const char* start = cleaned.c_str();
  char* end = nullptr;
  double d = std::strtod(start, &end);
  bool found_digit = false;
  for (const char* p = start; p < end; ++p) {
    if (*p >= '0' && *p <= '9') {
      found_digit = true;
      break;
    }
  }
  if (!found_digit) d = 0.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, 64, bits);
  result.is_real = true;
  return result;
}

static void StringXtoa(const StringMethodArgs& a, int base) {
  if (a.call_expr->args.empty()) return;
  uint64_t val =
      EvalExpr(a.call_expr->args[0], a.ctx, a.arena).ToUint64() & 0xFFFFFFFFULL;
  std::string result;
  if (base == 10) {
    result = std::to_string(static_cast<int32_t>(static_cast<uint32_t>(val)));
  } else if (base == 16) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llx",
                  static_cast<unsigned long long>(val));
    result = buf;
  } else if (base == 8) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llo",
                  static_cast<unsigned long long>(val));
    result = buf;
  } else if (base == 2) {
    if (val == 0) {
      result = "0";
    } else {
      while (val > 0) {
        result += static_cast<char>('0' + (val & 1));
        val >>= 1;
      }
      std::reverse(result.begin(), result.end());
    }
  }
  StoreString(a, result);
}

static void StringRealtoa(const StringMethodArgs& a) {
  if (a.call_expr->args.empty()) return;
  double d = RealVecToDouble(EvalExpr(a.call_expr->args[0], a.ctx, a.arena));
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%g", d);
  StoreString(a, buf);
}

static bool DispatchReturningMethod(std::string_view method,
                                    const StringMethodArgs& a, Logic4Vec& out) {
  if (method == "len") {
    out = StringLen(a.str, a.arena);
    return true;
  }
  if (method == "getc") {
    out = StringGetc(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "toupper") {
    out = StringToupper(a.str, a.arena);
    return true;
  }
  if (method == "tolower") {
    out = StringTolower(a.str, a.arena);
    return true;
  }
  if (method == "compare") {
    out = StringCompare(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "icompare") {
    out = StringIcompare(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "substr") {
    out = StringSubstr(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "atoi") {
    out = StringAtoBase(a.str, 10, a.arena);
    return true;
  }
  if (method == "atohex") {
    out = StringAtoBase(a.str, 16, a.arena);
    return true;
  }
  if (method == "atooct") {
    out = StringAtoBase(a.str, 8, a.arena);
    return true;
  }
  if (method == "atobin") {
    out = StringAtoBase(a.str, 2, a.arena);
    return true;
  }
  if (method == "atoreal") {
    out = StringAtoreal(a.str, a.arena);
    return true;
  }
  return false;
}

static bool DispatchMutatingMethod(std::string_view method,
                                   const StringMethodArgs& a, Logic4Vec& out) {
  if (!StringMethodWritesItsObject(method)) return false;
  if (method == "putc") {
    StringPutc(a);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "itoa") {
    StringXtoa(a, 10);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "hextoa") {
    StringXtoa(a, 16);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "octtoa") {
    StringXtoa(a, 8);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "bintoa") {
    StringXtoa(a, 2);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "realtoa") {
    StringRealtoa(a);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  return false;
}

static std::string PackageScopedKey(const Expr* scoped) {
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution || scoped->lhs == nullptr ||
      scoped->rhs == nullptr || scoped->lhs->kind != ExprKind::kIdentifier ||
      scoped->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return std::string(scoped->lhs->text) + "." + std::string(scoped->rhs->text);
}

static bool ExtractScopedStringMethodParts(const Expr* expr, std::string& key,
                                           std::string_view& method) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const Expr* scoped = access->lhs;
  if (scoped != nullptr && scoped->kind == ExprKind::kIdentifier &&
      scoped->scope_prefix == "$unit") {
    key = DeclaredKindsKey(scoped);
    method = access->rhs->text;
    return true;
  }
  key = PackageScopedKey(scoped);
  if (key.empty()) return false;
  method = access->rhs->text;
  return true;
}

struct PropertyShape {
  bool is_array = false;
  bool typedef_holds_strings = false;
};

static PropertyShape PropertyShapeOf(const ClassTypeInfo* type,
                                     std::string_view name, SimContext& ctx) {
  for (const ClassTypeInfo* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      const ModuleItem* item = PropertyNamedTypedef(member, t, ctx);
      PropertyShape shape;
      shape.is_array =
          !(item != nullptr ? item->unpacked_dims : member->unpacked_dims)
               .empty();
      shape.typedef_holds_strings =
          item != nullptr && item->typedef_type.kind == DataTypeKind::kString;
      return shape;
    }
  }
  return {};
}

bool PropertyIsString(const ClassTypeInfo* type, std::string_view name,
                      SimContext& ctx, bool elements) {
  const ClassTypeInfo::PropertyInfo* prop =
      type != nullptr ? type->FindProperty(name) : nullptr;
  if (prop == nullptr) return false;
  PropertyShape shape = PropertyShapeOf(type, name, ctx);
  return (prop->is_string || shape.typedef_holds_strings) &&
         shape.is_array == elements;
}

static bool IsNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsNamePath(e->lhs);
}

static const ClassTypeInfo* BareNameClassScope(std::string_view name,
                                               SimContext& ctx) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr) {
    const ClassTypeInfo* owner = method_cls->StaticPropertyOwner(name);
    return owner != nullptr ? owner : method_cls;
  }
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr ? self->type : nullptr;
}

static bool ReadBareStringProperty(const Expr* name, SimContext& ctx,
                                   Arena& arena, std::string& str) {
  if (name->text == "this" || NameDenotesVariable(name->text, ctx))
    return false;
  if (!PropertyIsString(BareNameClassScope(name->text, ctx), name->text, ctx))
    return false;
  str = Logic4VecToString(EvalExpr(name, ctx, arena));
  return true;
}

static bool ReadScopedStringProperty(const Expr* access, SimContext& ctx,
                                     Arena& arena, std::string& str) {
  if (access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!PropertyIsString(ctx.FindClassType(access->lhs->text), access->rhs->text,
                        ctx)) {
    return false;
  }
  str = Logic4VecToString(EvalExpr(access, ctx, arena));
  return true;
}

static bool ReadHandleStringProperty(const Expr* access, SimContext& ctx,
                                     Arena& arena, std::string& str) {
  if (!IsNamePath(access->lhs)) return false;
  const ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  if (obj == nullptr || !PropertyIsString(obj->type, access->rhs->text, ctx))
    return false;
  str = Logic4VecToString(obj->GetProperty(access->rhs->text, arena));
  return true;
}

static bool NamesArrayFormal(std::string_view name, SimContext& ctx) {
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  return info != nullptr &&
         ctx.FindLocalVariable(std::string(name) + "[" +
                               std::to_string(info->lo) + "]") != nullptr;
}

static bool DeclaredArrayHoldsStrings(std::string_view name, SimContext& ctx) {
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr)
    return (ctx.FindQueue(name) != nullptr ||
            ctx.FindAssocArray(name) != nullptr) &&
           ctx.IsStringVariable(name);
  return info->elem_type_kind == DataTypeKind::kString ||
         ctx.IsStringVariable(name) ||
         ctx.IsStringVariable(std::string(name) + "[" +
                              std::to_string(info->lo) + "]");
}

static bool ResolveStringPropertyTarget(const Expr* receiver, SimContext& ctx,
                                        FieldTarget& target,
                                        bool elements = false);

static bool SelectsMultiDimStringLeaf(const Expr* receiver, SimContext& ctx) {
  size_t selects = 0;
  const Expr* root = receiver;
  while (root != nullptr && root->kind == ExprKind::kSelect &&
         root->index_end == nullptr) {
    ++selects;
    root = root->base;
  }
  if (root == nullptr || root->kind != ExprKind::kIdentifier ||
      !NameDenotesVariable(root->text, ctx))
    return false;
  const ArrayInfo* info = ctx.FindArrayInfo(root->text);
  return info != nullptr && info->dim_sizes.size() >= 2 &&
         selects == info->dim_sizes.size() &&
         DeclaredArrayHoldsStrings(root->text, ctx);
}

static bool SelectsStringElement(const Expr* receiver, SimContext& ctx) {
  if (receiver->kind != ExprKind::kSelect || receiver->index_end != nullptr ||
      receiver->base == nullptr) {
    return false;
  }
  const Expr* base = receiver->base;
  if (base->kind == ExprKind::kIdentifier &&
      (NameDenotesVariable(base->text, ctx) ||
       NamesArrayFormal(base->text, ctx))) {
    return DeclaredArrayHoldsStrings(base->text, ctx);
  }
  if (SelectsMultiDimStringLeaf(receiver, ctx)) return true;
  if (const StructFieldInfo* member = ResolveStructArrayMember(base, ctx))
    return member->type_kind == DataTypeKind::kString;
  FieldTarget target;
  if (ResolveStringPropertyTarget(base, ctx, target, true)) return true;
  return DeclaredArrayHoldsStrings(PackageScopedKey(base), ctx);
}

static bool SelectsStringMember(const Expr* receiver, SimContext& ctx) {
  FieldTarget target = ResolveFieldTarget(receiver, ctx);
  return target.kind == FieldTarget::Kind::kBits &&
         target.member_kind == DataTypeKind::kString;
}

static bool ReadStringReceiver(const Expr* receiver, SimContext& ctx,
                               Arena& arena, std::string& str) {
  if (receiver == nullptr) return false;
  if (SelectsStringElement(receiver, ctx)) {
    str = Logic4VecToString(EvalExpr(receiver, ctx, arena));
    return true;
  }
  if (receiver->kind == ExprKind::kIdentifier)
    return ReadBareStringProperty(receiver, ctx, arena, str);
  if (receiver->kind != ExprKind::kMemberAccess || receiver->lhs == nullptr ||
      receiver->rhs == nullptr ||
      receiver->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (receiver->is_scope_resolution)
    return ReadScopedStringProperty(receiver, ctx, arena, str);
  if (SelectsStringMember(receiver, ctx)) {
    str = Logic4VecToString(EvalExpr(receiver, ctx, arena));
    return true;
  }
  return ReadHandleStringProperty(receiver, ctx, arena, str);
}

static const ClassTypeInfo* TargetClassType(const FieldTarget& target) {
  if (target.kind == FieldTarget::Kind::kStatic) return target.type;
  if (target.kind != FieldTarget::Kind::kProperty || target.obj == nullptr)
    return nullptr;
  return target.type != nullptr ? target.type : target.obj->type;
}

static bool ResolveStringPropertyTarget(const Expr* receiver, SimContext& ctx,
                                        FieldTarget& target, bool elements) {
  if (receiver->kind == ExprKind::kIdentifier) {
    if (NameDenotesVariable(receiver->text, ctx)) return false;
    target = ResolveBarePropertyTarget(receiver->text, ctx);
  } else if (receiver->kind == ExprKind::kMemberAccess) {
    target = ResolveFieldTarget(receiver, ctx);
  } else {
    return false;
  }
  return PropertyIsString(TargetClassType(target), target.field, ctx, elements);
}

static std::string StringPropertyText(const FieldTarget& target, Arena& arena) {
  if (target.kind == FieldTarget::Kind::kStatic)
    return Logic4VecToString(*target.slot);
  return Logic4VecToString(
      target.type != nullptr
          ? target.obj->GetPropertyForType(target.field, target.type, arena)
          : target.obj->GetProperty(target.field, arena));
}

bool TryEvalStringMethodOnValue(const Logic4Vec& value, const Expr* call_expr,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  std::string_view method = call_expr->lhs->rhs->text;
  if (!StringMethodAnswersAValue(method)) return false;
  StringMethodArgs args{nullptr,   nullptr, Logic4VecToString(value),
                        call_expr, ctx,     arena};
  return DispatchReturningMethod(method, args, out);
}

static bool TryEvalStringMethodOnReceiver(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view method = access->rhs->text;
  if (StringMethodAnswersAValue(method)) {
    std::string str;
    if (!ReadStringReceiver(access->lhs, ctx, arena, str)) return false;
    StringMethodArgs args{nullptr, nullptr, str, expr, ctx, arena};
    return DispatchReturningMethod(method, args, out);
  }
  if (!StringMethodWritesItsObject(method)) return false;
  if (SelectsStringElement(access->lhs, ctx)) {
    StringMethodArgs args{nullptr,
                          nullptr,
                          Logic4VecToString(EvalExpr(access->lhs, ctx, arena)),
                          expr,
                          ctx,
                          arena,
                          access->lhs};
    return DispatchMutatingMethod(method, args, out);
  }
  FieldTarget target;
  if (!ResolveStringPropertyTarget(access->lhs, ctx, target)) return false;
  StringMethodArgs args{nullptr, &target, StringPropertyText(target, arena),
                        expr,    ctx,     arena};
  return DispatchMutatingMethod(method, args, out);
}

bool NamesStringProperty(const Expr* e, SimContext& ctx) {
  FieldTarget target;
  return ResolveStringPropertyTarget(e, ctx, target);
}

bool TryWriteStringPropertyChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr ||
      lhs->index_end != nullptr) {
    return false;
  }
  FieldTarget target;
  if (!ResolveStringPropertyTarget(lhs->base, ctx, target)) return false;
  Logic4Vec idx = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx)) return true;
  std::string text = StringPropertyText(target, arena);
  auto i = idx.ToUint64();
  auto byte = static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF);
  if (i >= text.size() || byte == 0) return true;
  text[i] = static_cast<char>(byte);
  WriteResolvedField(target, StringToLogic4Vec(arena, text), ctx, arena);
  return true;
}

bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  MethodCallParts parts;
  std::string scoped_key;
  if (ExtractScopedStringMethodParts(expr, scoped_key, parts.method_name)) {
    parts.var_name = scoped_key;
  } else if (!ExtractMethodCallParts(expr, parts)) {
    return TryEvalStringMethodOnReceiver(expr, ctx, arena, out);
  }

  if (!ctx.IsStringVariable(parts.var_name) ||
      !NameDenotesVariable(parts.var_name, ctx)) {
    return TryEvalStringMethodOnReceiver(expr, ctx, arena, out);
  }

  auto* var = ctx.FindVariable(parts.var_name);
  std::string str = var ? Logic4VecToString(var->value) : "";

  StringMethodArgs args{var, nullptr, str, expr, ctx, arena};
  if (DispatchReturningMethod(parts.method_name, args, out)) return true;
  return DispatchMutatingMethod(parts.method_name, args, out);
}

bool TryEvalStringProperty(std::string_view var_name, std::string_view prop,
                           SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!ctx.IsStringVariable(var_name)) return false;
  if (prop != "len") return false;
  auto* var = ctx.FindVariable(var_name);
  std::string str = var ? Logic4VecToString(var->value) : "";
  out = StringLen(str, arena);
  return true;
}

bool TryEvalStringMethodWithoutParens(const Expr* access, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  if (access->kind != ExprKind::kMemberAccess || access->is_scope_resolution ||
      access->with_expr != nullptr || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier ||
      !StringMethodAnswersAValue(access->rhs->text)) {
    return false;
  }
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = const_cast<Expr*>(access);
  call->range = access->range;
  return TryEvalStringMethodCall(call, ctx, arena, out);
}

}  // namespace delta
