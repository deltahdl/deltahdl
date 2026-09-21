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
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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

// One string method call: the string it is called on, as text, and where
// that string lives -- `var` for a string variable of the run's tables, else
// `target` for a class property resolved to its storage (§8.5, §8.9), which
// the six methods that write their object store through; a method that
// answers a value reads `str` alone and both may be null.
struct StringMethodArgs {
  Variable* var;
  const FieldTarget* target;
  std::string str;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
};

// §6.16.2 and §6.16.11 through §6.16.15: the text a mutating method leaves
// in its object, stored where the object lives. A property takes it as an
// assignment to the property does (WriteResolvedField), whole, since §6.16
// gives a string no declared width to truncate to.
static void StoreString(const StringMethodArgs& a, std::string_view text) {
  if (a.var != nullptr) {
    a.var->value = StringToLogic4Vec(a.arena, text);
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

// §6.16.4, §6.16.5 and §6.16.8 declare toupper, tolower and substr with a
// string result, and the value answered carries the kind so that a method
// called on it, `s.toupper().substr(0, 2)`, reads it as text
// (TryEvalCallResultMethodCall); StringToLogic4Vec alone leaves the words a
// packed number.
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

static Logic4Vec StringCompare(const std::string& str, const Expr* call_expr,
                               SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  int cmp = str.compare(other);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
}

static Logic4Vec StringIcompare(const std::string& str, const Expr* call_expr,
                                SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  std::string a = str;
  std::string b = other;
  for (auto& c : a) c = static_cast<char>(std::tolower(c));
  for (auto& c : b) c = static_cast<char>(std::tolower(c));
  int cmp = a.compare(b);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
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
  // The scan conforms to real-constant syntax (§5.7.2), which permits an
  // underscore between digits purely as a spacing separator. strtod would stop
  // at such an underscore, so first drop the underscores that fall between two
  // digits; any other underscore is left in place and still terminates the
  // scan, since it does not conform to the real-constant syntax.
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
  // The conversion only recognizes real constants, and the result is zero when
  // no digits were scanned. strtod additionally accepts digit-free spellings
  // such as "inf"/"nan"; these are not real constants, so force the result to
  // zero unless the scanned prefix actually contained a decimal digit.
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
  // atoreal yields a real value; flag the result so assignments and expression
  // operands treat the 64 bits as an IEEE double rather than an integer.
  auto result = MakeLogic4VecVal(arena, 64, bits);
  result.is_real = true;
  return result;
}

static void StringXtoa(const StringMethodArgs& a, int base) {
  if (a.call_expr->args.empty()) return;
  auto val = EvalExpr(a.call_expr->args[0], a.ctx, a.arena).ToUint64();
  std::string result;
  if (base == 10) {
    result = std::to_string(val);
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
  // The six names are StringMethodWritesItsObject's, so that the elaborator's
  // §6.20 refusal of one of these calls on a constant and the write carried out
  // here can never be about different sets of methods.
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

// §26.3: a package's string variable named through the package scope
// resolution operator, `P::ps.len()`, is a method call whose receiver is the
// scoped name rather than an identifier, which ExtractMethodCallParts reads
// alone; the variable is held under the "P.ps" key the lowerer creates it
// with (InitPackageDataVariables), so the receiver is that key. §3.12.1
// (printed page 56): `$unit::s.len()` is likewise the unit's string under
// "$unit.s" past a module's own s, the identifier carrying the prefix the
// parser keeps (DeclaredKindsKey); read as a bare identifier by
// ExtractMethodCallParts, the module's s answered. Answers the key and the
// method for those shapes, and false for any other.
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
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution || scoped->lhs == nullptr ||
      scoped->rhs == nullptr || scoped->lhs->kind != ExprKind::kIdentifier ||
      scoped->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  key = std::string(scoped->lhs->text) + "." + std::string(scoped->rhs->text);
  method = access->rhs->text;
  return true;
}

// §6.16 with §8.7: whether `type`, or a class it extends, declares the
// property `name` with the string type.
static bool PropertyIsString(const ClassTypeInfo* type, std::string_view name) {
  const ClassTypeInfo::PropertyInfo* prop =
      type != nullptr ? type->FindProperty(name) : nullptr;
  return prop != nullptr && prop->is_string;
}

// Whether `e` is a name or a chain of member selects down from one, `h` or
// `d.c`: reading it runs no subroutine, so it can be evaluated to find the
// object it denotes and evaluated again by whichever dispatcher takes the call
// when it denotes no string.
static bool IsNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsNamePath(e->lhs);
}

// §6.16 with §8.10 and §8.11: the class scope a bare name inside a method
// resolves against -- the class whose static property it names, the running
// method's class, or the object's own -- as EvalIdentifierClassScope
// (evaluation.cpp) resolves it; nullptr outside every method.
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

// The text of a string property named bare inside a method of its class
// (§8.6, §8.10). A variable of the name is what the identifier denotes
// instead (§23.9), and a string one is TryEvalStringMethodCall's own case;
// `this` names no property.
static bool ReadBareStringProperty(const Expr* name, SimContext& ctx,
                                   Arena& arena, std::string& str) {
  if (name->text == "this" || NameDenotesVariable(name->text, ctx))
    return false;
  if (!PropertyIsString(BareNameClassScope(name->text, ctx), name->text))
    return false;
  str = Logic4VecToString(EvalExpr(name, ctx, arena));
  return true;
}

// The text of a static string property named through the class scope
// resolution operator, `C::name` (§8.9).
static bool ReadScopedStringProperty(const Expr* access, SimContext& ctx,
                                     Arena& arena, std::string& str) {
  if (access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!PropertyIsString(ctx.FindClassType(access->lhs->text),
                        access->rhs->text)) {
    return false;
  }
  str = Logic4VecToString(EvalExpr(access, ctx, arena));
  return true;
}

// The text of a string property reached through a handle or a chain of them,
// `h.s`, `this.s` or `d.c.s` (§8.3, §8.11); the handle side is a name path,
// so reading it to find the object runs nothing.
static bool ReadHandleStringProperty(const Expr* access, SimContext& ctx,
                                     Arena& arena, std::string& str) {
  if (!IsNamePath(access->lhs)) return false;
  const ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  if (obj == nullptr || !PropertyIsString(obj->type, access->rhs->text))
    return false;
  str = Logic4VecToString(obj->GetProperty(access->rhs->text, arena));
  return true;
}

// §6.16 declares the string methods on the string type, so a method is called
// on any expression of that type, and the receivers of this file's other two
// readers -- a string variable of the run's tables, a package's under its
// scoped key -- are two of them. The text of the others, when the declaration
// behind the receiver wrote the string type: a class property named bare
// inside a method of the class, a static property named bare in a static
// method or as `C::name`, or a property reached through a handle or a chain
// of them. The declaration is asked because the value read is not: a literal
// stored into the property is a packed value (§5.9) that carries no kind.
// Answers false for any other receiver, a call's result among them, which
// TryEvalCallResultMethodCall reads by the kind the call's value carries.
static bool ReadStringReceiver(const Expr* receiver, SimContext& ctx,
                               Arena& arena, std::string& str) {
  if (receiver == nullptr) return false;
  if (receiver->kind == ExprKind::kIdentifier)
    return ReadBareStringProperty(receiver, ctx, arena, str);
  if (receiver->kind != ExprKind::kMemberAccess || receiver->lhs == nullptr ||
      receiver->rhs == nullptr ||
      receiver->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (receiver->is_scope_resolution)
    return ReadScopedStringProperty(receiver, ctx, arena, str);
  return ReadHandleStringProperty(receiver, ctx, arena, str);
}

// The class type whose declaration of `target.field` says what the storage
// holds: the declared class scoping a property write (§8.15), else the
// object's own, and the declaring class of a static property.
static const ClassTypeInfo* TargetClassType(const FieldTarget& target) {
  if (target.kind == FieldTarget::Kind::kStatic) return target.type;
  if (target.kind != FieldTarget::Kind::kProperty || target.obj == nullptr)
    return nullptr;
  return target.type != nullptr ? target.type : target.obj->type;
}

// §6.16.2 and §6.16.11 through §6.16.15, with §6.16's indexed character
// assignment: the storage a string that is no variable of the run's tables is
// written in -- a class property named bare inside a method of the class or
// through `this` (§8.11), a static property named bare in a static method or
// as `C::name` (§8.9, §8.10), or a property reached through a handle or a
// chain of them (§8.3) -- resolved as an assignment to the property resolves
// it (ResolveBarePropertyTarget, ResolveFieldTarget), when the declaration
// wrote the string type. A bare name a variable denotes (§23.9) is that
// variable's, which the callers serve first, and is not resolved here.
static bool ResolveStringPropertyTarget(const Expr* receiver, SimContext& ctx,
                                        FieldTarget& target) {
  if (receiver->kind == ExprKind::kIdentifier) {
    if (NameDenotesVariable(receiver->text, ctx)) return false;
    target = ResolveBarePropertyTarget(receiver->text, ctx);
  } else if (receiver->kind == ExprKind::kMemberAccess) {
    target = ResolveFieldTarget(receiver, ctx);
  } else {
    return false;
  }
  return PropertyIsString(TargetClassType(target), target.field);
}

// The text the resolved string property holds.
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

// The string methods on a receiver that is no string variable of the run's
// tables: a value-answering one reads the receiver ReadStringReceiver reads,
// and one that writes its object writes the property storage
// ResolveStringPropertyTarget resolves. The name is asked first so that a
// receiver is evaluated for a string method alone: a call of a class's own
// method on a chain of handles is left to the dispatcher that runs it, its
// receiver read once, there.
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
  FieldTarget target;
  if (!ResolveStringPropertyTarget(access->lhs, ctx, target)) return false;
  StringMethodArgs args{nullptr, &target, StringPropertyText(target, arena),
                        expr,    ctx,     arena};
  return DispatchMutatingMethod(method, args, out);
}

bool TryWriteStringPropertyChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr ||
      lhs->index_end != nullptr) {
    return false;
  }
  FieldTarget target;
  if (!ResolveStringPropertyTarget(lhs->base, ctx, target)) return false;
  // §6.16 (printed page 113): the index addresses one character, and an
  // index out of range or a null character written leaves the string as it
  // is, the rules StringWriteByte applies to a variable; an unknown index
  // addresses no character at all.
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

  // §23.9 with §8.6: a bare name inside a method that the class scope declares
  // is the property, not a like-named string of the enclosing module, which
  // NameDenotesVariable tells apart as EvalIdentifier does; asked of the
  // tables alone, `s.len()` in a method read the module's s.
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

}  // namespace delta
