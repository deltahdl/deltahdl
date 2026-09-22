#include "simulator/evaluation.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_instance_task.h"
#include "simulator/evaluation_internal.h"
#include "simulator/instance_bindings.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
// AssertionSampleStore, the §16.5.1 sampled values a concurrent assertion
// reads.
#include "simulator/sva_engine_sampling.h"

namespace delta {
// Resolves an unqualified identifier that is not a local variable against the
// running method's class scope. §8.10: a static method can directly access
// static properties of the same class by unqualified reference. §8.6/§8.15: an
// instance method reads it as a property of `this`, resolved against the class
// in which the running method is defined so a base method reads the base field
// even when a derived class shadows the name.
// §8.25: whether `name` is a value parameter of the class `decl` declares,
// one of its parameter port list.
static bool DeclaresValueParam(const ClassDecl* decl, std::string_view name) {
  if (decl == nullptr) return false;
  for (const auto& [pname, pexpr] : decl->params) {
    if (pname == name) return decl->type_param_names.count(name) == 0;
  }
  return false;
}

static Logic4Vec EvalIdentifierClassScope(const Expr* expr, SimContext& ctx,
                                          Arena& arena) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  auto* self = ctx.CurrentThis();
  // §8.25: a value parameter read inside a method of a specialized class is
  // the value the object's specialization bound it to, held on the object
  // (ApplyClassParamOverrides), and the class's own storage holds the
  // default alone, so the object is asked first where there is one.
  if (self != nullptr && method_cls != nullptr &&
      DeclaresValueParam(method_cls->decl, expr->text)) {
    auto it = self->properties.find(std::string(expr->text));
    if (it != self->properties.end()) return it->second;
  }
  // §8.23: the class's own static property, or one of a class lexically
  // containing it, which a nested class's method names unqualified; §8.13
  // (printed pages 189-190): or a base class's, read from that class's own
  // storage, so D's method's bare `n` reads what `C::n = 4` wrote where D
  // extends C, where asked of D's own static_properties it read 0.
  const ClassTypeInfo* owner =
      method_cls ? method_cls->StaticPropertyOwner(expr->text) : nullptr;
  if (owner)
    return owner->static_properties.find(std::string(expr->text))->second;
  // §6.19: a literal of an enumeration the class declares, tried before the
  // property read, which answers a value for an unknown name all the same.
  const ClassTypeInfo* scope = method_cls ? method_cls
                               : self     ? self->type
                                          : nullptr;
  Logic4Vec literal;
  if (TryClassScopeEnumLiteral(expr->text, scope, arena, literal))
    return literal;
  // §13.5.5: a method of the class named bare is its call, `m` as `m()`.
  if (TryEvalParenFreeMethodCall(expr, ctx, arena, literal)) return literal;
  if (!self) return MakeLogic4Vec(arena, 1);
  if (method_cls)
    return self->GetPropertyForType(expr->text, method_cls, arena);
  return self->GetProperty(expr->text, arena);
}

// §8.13: whether the class scope a bare name inside a method resolves against
// declares `name`, as a static property of the running method's class or as a
// property of the object's class or one it inherits from. The class scope is
// searched before the scope enclosing the class, so a name it declares is
// never the instance of the same name in the enclosing module.
static bool ClassScopeDeclares(std::string_view name, SimContext& ctx) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr && method_cls->StaticPropertyOwner(name) != nullptr)
    return true;
  const ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* scope = method_cls != nullptr ? method_cls
                               : self != nullptr     ? self->type
                                                     : nullptr;
  return scope != nullptr && scope->FindProperty(name) != nullptr;
}

bool NameDenotesVariable(std::string_view name, SimContext& ctx) {
  if (ctx.FindVariable(name) == nullptr) return false;
  if (ctx.FindLocalVariable(name) != nullptr) return true;
  return !ClassScopeDeclares(name, ctx);
}

// §25.9: an interface instance named where a value is wanted -- the right
// side of an assignment to a virtual interface, an argument to a subroutine or
// to new(), an operand of == -- is the handle of that instance, the value a
// virtual interface holds to represent it. It is answered only for a name no
// variable, let or class scope declares, since an instance name is visible
// from the module instantiating it and from the classes declared there alone.
static bool TryInterfaceInstanceHandle(std::string_view name, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (ClassScopeDeclares(name, ctx)) return false;
  std::string scope = ctx.ResolveInstanceScope(name);
  if (scope.empty()) return false;
  out = MakeLogic4VecVal(arena, 64, ctx.VirtualInterfaceHandle(scope));
  return true;
}

// §16.14.6.1: the value the instance of a procedural concurrent assertion
// being evaluated saved for `expr` when it was queued, a const cast's or an
// automatic variable's, or nullptr where no instance is being evaluated or
// the instance saved none for the site.
static const Logic4Vec* BoundInstanceValue(const Expr* expr, SimContext& ctx) {
  const InstanceBindings* bindings = ctx.AssertionSamples().Bindings();
  return bindings == nullptr ? nullptr : bindings->Find(expr);
}

// The real and string kinds the declaration registered under `name`, given
// to the value read from it: a package's or the unit's item under its
// qualified key (ShapePackageVariable in lowerer_package_data.cpp), a
// module's under the identifier's text. §6.12: the real kind is also read off
// the variable itself, which is where a subroutine's `real a` formal and
// `real l` local carry it (BindValueArg, CreateFuncLocalVar) -- no name table
// holds them, since one keyed by the bare text would make every `a` in the
// design a real.
static void MarkDeclaredKinds(Logic4Vec& val, std::string_view name,
                              const Variable& var, SimContext& ctx) {
  if (var.is_real || ctx.IsRealVariable(name)) val.is_real = true;
  if (ctx.IsStringVariable(name)) val.is_string = true;
}

// §13.5.5 (printed page 351): a member select naming a class method, `C::m`
// or `h.m`, is the method's call; any other is the member's read.
static Logic4Vec EvalMemberAccessOrCall(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  Logic4Vec call;
  if (TryEvalParenFreeMethodCall(expr, ctx, arena, call)) return call;
  return EvalMemberAccess(expr, ctx, arena);
}

static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  // §8.11: "The this keyword denotes a predefined object handle that refers to
  // the object that was used to invoke the subroutine that this is used
  // within." A bare `this` arrives as an ExprKind::kIdentifier node whose text
  // is the keyword, Parser::ParseMemberAccessChain in
  // src/parser/expr_parser.cpp building one for it, so it is answered here and
  // reaches every reader of an expression rather than one site.
  //
  // It is answered before SimContext::FindVariable, which no source can reach
  // first because `this` is a keyword and names no variable. Left to fall
  // through, the name reached EvalIdentifierClassScope below and was looked up
  // as a property called "this", which no class declares, so the value handed
  // back was not a handle at all. TryClassCopyNewAssign in
  // src/simulator/statement_assign_core.cpp then found no object for
  // `p2 = new this;` and let TryClassNewAssign construct a fresh one, breaching
  // all three steps §8.12 gives the shallow copy.
  if (expr->text == "this") {
    return MakeLogic4VecVal(arena, 64, ctx.CurrentThisHandle());
  }
  // §23.6: a leading `$root` makes the name absolute from the top of the
  // instantiated design, and §3.12.1 a leading `$unit::` the compilation
  // unit's own declaration, past any module's; the parser keeps either in
  // Expr::scope_prefix rather than in the identifier's text
  // (Parser::MakeSysScopePrefix in src/parser/expr_parser_calls.cpp).
  // Reading the text alone drops it and resolves the name in whichever
  // instance is running, so `$unit::g` in a module declaring its own g
  // read the module's. ResolveSignalToVariable in src/simulator/awaiters.h
  // spells the `$root` name the same way, so an event control and an
  // expression reading one signal reach one variable, and the argument
  // binds of eval_function_args.cpp bind a ref formal by the same key
  // (IdentifierLookupKey, eval_function_args_scoped.cpp). The unit's kinds
  // stand under its key as its storage does, a `$root` name's under the
  // text, as before (DeclaredKindsKey, which the store side asks by too).
  std::string scoped_name = IdentifierLookupKey(expr);
  std::string_view lookup_name = scoped_name;
  std::string kinds_name = DeclaredKindsKey(expr);
  // §23.9 with §8.6: the class scope is searched before the scope enclosing
  // the class, so a property named bare in a method is read as the property
  // even where the instantiating module declares a variable of that name; a
  // local of the method shadows both. Before this the module's variable won
  // and the method read and wrote the wrong object.
  auto* var = NameDenotesVariable(lookup_name, ctx)
                  ? ctx.FindVariable(lookup_name)
                  : nullptr;
  if (!var) {
    // §11.12 — a no-argument let referenced without parentheses appears here
    // as a bare identifier. Expand its body at each use (re-evaluated, not
    // snapshotted) before falling back to class-scope resolution.
    if (auto* let_decl = ctx.FindLetDecl(expr->text);
        let_decl && let_decl->func_args.empty()) {
      return EvalLetExpansion(let_decl, expr, ctx, arena);
    }
    Logic4Vec instance;
    if (TryInterfaceInstanceHandle(expr->text, ctx, arena, instance))
      return instance;
    return EvalIdentifierClassScope(expr, ctx, arena);
  }
  if (var->is_event)
    return MakeLogic4VecVal(arena, 1, var->is_null_event ? 0u : 1u);
  auto val = var->value;
  // §16.5.2: "In an assertion, the sampled value is the only valid value of a
  // variable during a clock tick." While a clocked concurrent assertion's
  // property is being evaluated, a variable named in it therefore reads the
  // value §16.5.1 samples for this time slot rather than the value standing
  // now. The store answers nothing for a variable no such assertion reads and
  // nothing at all outside such an evaluation, so every other read of a
  // variable in the design is the live read it was before.
  const Logic4Vec* sampled =
      ctx.AssertionSamples().ReadWithinProperty(var, ctx.CurrentTime());
  if (sampled != nullptr) val = *sampled;
  MarkDeclaredKinds(val, kinds_name, *var, ctx);
  // An object's signedness is fixed by its own declaration; it is never
  // inherited from a value that flowed in from elsewhere (e.g. across a
  // module port). Derive the read value's signedness from the declaration
  // so a signed value stored into an unsigned object reads back unsigned.
  val.is_signed = var->is_signed;
  // §5.7.1: what is read is the variable's value and no literal, so a 1-bit
  // variable set from `'1` reads as a 1-bit 1 that zero-extends, whatever
  // the value it was set from would have filled.
  val.fills_width = false;
  return val;
}
bool HasUnknownBits(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].bval != 0) return true;
  }
  return false;
}
// §6.8, Table 6-7's 'x, and the value §11.4.x gives an operation whose operand
// carries an unknown bit. Only the bits the width names are x: MakeLogic4Vec
// rounds up to whole words, and every bit above the width in the top word
// stays clear, because §11.4.5 has === compare the x and z bits of its
// operands and EvalCaseEquality compares them a word at a time. Filling those
// bits left an all-x value built here comparing unequal to an all-x value of
// the same declared type built by SimContext::CreateVariable, which masks --
// `logic [7:0] arr [0:2]` against a `logic [7:0]` scalar of the same Table 6-7
// default, and `(-a) === 4'bxxxx` with no array in sight.
Logic4Vec MakeAllX(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  FillWithX(vec);
  return vec;
}

// §28.12: a value every bit of which is high impedance, which is what a source
// driving none of a net contributes to resolution -- a driver at z drives
// nothing, so the bits a partial driver leaves at z are resolved by the net's
// other sources alone. Only the bits the width names are set, the rest of the
// last word staying clear so that nothing above the value reads as driven.
Logic4Vec MakeAllHighZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    vec.words[i] = {0, WordMaskWithinWidth(width, i)};
  }
  return vec;
}

// Writes the low `w` bits of {aval,bval} into `result` starting at bit_pos,
// spanning the 64-bit word boundary when the chunk straddles two words.
static void WriteConcatChunk(Logic4Vec& result, uint32_t bit_pos, uint32_t w,
                             uint64_t aval, uint64_t bval) {
  uint32_t word = bit_pos / 64;
  uint32_t bit = bit_pos % 64;
  if (word >= result.nwords) return;
  result.words[word].aval |= aval << bit;
  result.words[word].bval |= bval << bit;
  if (bit + w > 64 && word + 1 < result.nwords) {
    result.words[word + 1].aval |= aval >> (64 - bit);
    result.words[word + 1].bval |= bval >> (64 - bit);
  }
}

Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena) {
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    // Concatenation places each operand's bits verbatim, so preserve the raw
    // 4-state encoding (aval/bval, not ToUint64()); copy every word so operands
    // wider than 64 bits (e.g. multi-character strings) are not truncated.
    uint32_t remaining = it->width;
    for (uint32_t pw = 0; pw < it->nwords && remaining > 0; ++pw) {
      uint32_t w = (remaining > 64) ? 64 : remaining;
      WriteConcatChunk(result, bit_pos, w, it->words[pw].aval,
                       it->words[pw].bval);
      bit_pos += w;
      remaining -= w;
    }
  }
  return result;
}

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  bool any_string = false;
  std::vector<Logic4Vec> parts;
  // §11.4.12: every operand of a concatenation is self-determined, an
  // unbased unsized literal among them one bit wide (§5.7.1).
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    if (parts.back().is_string) any_string = true;
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  auto result = AssembleConcatParts(parts, total_width, arena);
  result.is_string = any_string;
  return result;
}

static uint32_t AssignExprLhsWidth(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kConcatenation) {
    uint32_t total = 0;
    for (auto* elem : lhs->elements) total += AssignExprLhsWidth(elem, ctx);
    return total;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  return var ? var->value.width : 0;
}

static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  uint32_t lhs_w = AssignExprLhsWidth(expr->lhs, ctx);
  if (lhs_w == 0) return rhs_val;
  PerformBlockingAssign(expr->lhs, rhs_val, ctx, arena);
  // §11.3.6: a concatenation target yields an unsigned integral result whose
  // width is the sum of its operand widths. Re-pack the value rather than
  // forwarding the right-hand side so the result never inherits the
  // right-hand side's signedness, even when the widths already match.
  bool lhs_is_concat = expr->lhs->kind == ExprKind::kConcatenation;
  if (lhs_w == rhs_val.width && !lhs_is_concat) return rhs_val;
  uint64_t v = rhs_val.ToUint64();
  if (lhs_w < 64) v &= (uint64_t{1} << lhs_w) - 1;
  return MakeLogic4VecVal(arena, lhs_w, v);
}

static bool ArrayElementsEqual(std::string_view a, const ArrayInfo* ai,
                               std::string_view b, SimContext& ctx) {
  for (uint32_t i = 0; i < ai->size; ++i) {
    auto an = std::string(a) + "[" + std::to_string(ai->lo + i) + "]";
    auto bn = std::string(b) + "[" + std::to_string(ai->lo + i) + "]";
    auto* av = ctx.FindVariable(an);
    auto* bv = ctx.FindVariable(bn);
    if (!av || !bv) return false;
    if (av->value.ToUint64() != bv->value.ToUint64()) return false;
  }
  return true;
}

static bool TryArrayEqualityOp(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq)
    return false;
  if (!expr->lhs || !expr->rhs) return false;
  if (expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->kind != ExprKind::kIdentifier) return false;
  auto* la = ctx.FindArrayInfo(expr->lhs->text);
  auto* ra = ctx.FindArrayInfo(expr->rhs->text);
  if (!la || !ra) return false;
  bool eq = (la->size == ra->size && la->elem_width == ra->elem_width);
  if (eq) eq = ArrayElementsEqual(expr->lhs->text, la, expr->rhs->text, ctx);
  uint64_t val = (expr->op == TokenKind::kEqEq) == eq ? 1 : 0;
  out = MakeLogic4VecVal(arena, 1, val);
  return true;
}

static Logic4Vec EvalLogicalAnd(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 1);
}

static Logic4Vec EvalLogicalOr(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalImpl(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalEquiv(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  bool r_unknown = HasUnknownBits(r);
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  bool lv = l.ToUint64() != 0;
  bool rv = r.ToUint64() != 0;
  return MakeLogic4VecVal(arena, 1, (lv == rv) ? 1 : 0);
}
// Operands of an identity-equality comparison, after resolving each side's
// identifier node, bound variable, and null/event classification.
struct IdentityEqualityOperands {
  const Expr* lhs_id;
  const Expr* rhs_id;
  Variable* lv;
  Variable* rv;
  bool lhs_is_event;
  bool rhs_is_event;
  bool lhs_is_null;
  bool rhs_is_null;
  bool is_eq_op;
};

// Returns true when the operator is one of the four equality operators
// (==, !=, ===, !==) and fills `ops` with the resolved operand information.
static bool ResolveIdentityEqualityOperands(const Expr* expr, SimContext& ctx,
                                            IdentityEqualityOperands& ops) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq &&
      expr->op != TokenKind::kEqEqEq && expr->op != TokenKind::kBangEqEq) {
    return false;
  }
  ops.lhs_id = (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier)
                   ? expr->lhs
                   : nullptr;
  ops.rhs_id = (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
                   ? expr->rhs
                   : nullptr;
  ops.lv = ops.lhs_id ? ctx.FindVariable(ops.lhs_id->text) : nullptr;
  ops.rv = ops.rhs_id ? ctx.FindVariable(ops.rhs_id->text) : nullptr;
  ops.lhs_is_event = ops.lv && ops.lv->is_event;
  ops.rhs_is_event = ops.rv && ops.rv->is_event;
  ops.lhs_is_null = ops.lhs_id && ops.lhs_id->text == "null" && !ops.lv;
  ops.rhs_is_null = ops.rhs_id && ops.rhs_id->text == "null" && !ops.rv;
  ops.is_eq_op =
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kEqEqEq);
  return true;
}

// Compares two event operands by object identity (a null event compares equal
// to an unbound/null event), producing the boolean comparison result.
static Logic4Vec EvalEventIdentityEquality(const IdentityEqualityOperands& ops,
                                           Arena& arena) {
  bool equal = false;
  if (ops.lhs_is_event && ops.rhs_is_event) {
    equal = (ops.lv == ops.rv);
  } else if (ops.lhs_is_event && ops.rhs_is_null) {
    equal = ops.lv->is_null_event;
  } else if (ops.rhs_is_event && ops.lhs_is_null) {
    equal = ops.rv->is_null_event;
  }
  return MakeLogic4VecVal(arena, 1, (ops.is_eq_op == equal) ? 1u : 0u);
}

// §25.9: equality of a virtual interface against another virtual interface,
// an interface instance, or null compares the interface instance each side
// refers to (an unbound virtual interface and null compare equal).
static Logic4Vec EvalVirtualInterfaceEquality(
    const IdentityEqualityOperands& ops, SimContext& ctx, bool lhs_is_vi,
    bool rhs_is_vi, Arena& arena) {
  auto operand_scope = [&](Variable* v, const Expr* id, bool is_vi,
                           bool is_null) -> std::string {
    if (is_vi) return std::string(ctx.VirtualInterfaceBinding(v));
    if (is_null) return std::string();
    if (id) return ctx.ResolveInstanceScope(id->text);
    return std::string();
  };
  std::string ls =
      operand_scope(ops.lv, ops.lhs_id, lhs_is_vi, ops.lhs_is_null);
  std::string rs =
      operand_scope(ops.rv, ops.rhs_id, rhs_is_vi, ops.rhs_is_null);
  bool equal = (ls == rs);
  return MakeLogic4VecVal(arena, 1, (ops.is_eq_op == equal) ? 1u : 0u);
}

// Handles equality comparisons (==, !=, ===, !==) whose operands are event
// variables or virtual interfaces, per the special object-identity semantics.
// Returns true and sets `out` when the special handling applies; otherwise
// returns false so the caller falls through to the generic binary operator.
static bool TryEvalIdentityEquality(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  IdentityEqualityOperands ops;
  if (!ResolveIdentityEqualityOperands(expr, ctx, ops)) return false;
  if (ops.lhs_is_event || ops.rhs_is_event) {
    out = EvalEventIdentityEquality(ops, arena);
    return true;
  }
  bool lhs_is_vi = ctx.IsVirtualInterfaceVar(ops.lv);
  bool rhs_is_vi = ctx.IsVirtualInterfaceVar(ops.rv);
  if (lhs_is_vi || rhs_is_vi) {
    out = EvalVirtualInterfaceEquality(ops, ctx, lhs_is_vi, rhs_is_vi, arena);
    return true;
  }
  return false;
}

// §11.6.1 Table 11-21: arithmetic and bitwise operators whose result width is
// the maximum width of the two operands; both operands are context-determined.
static bool IsMaxWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

// §11.6.1: shift and power operators whose result width is the left operand's
// width; the left operand is context-determined, the right self-determined.
static bool IsLeftWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPower:
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return true;
    default:
      return false;
  }
}

static bool IsUnaryReductionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

// §11.6.1: the self-determined bit length of an expression, resolving variable
// widths through the simulation context. Returns 0 ("indeterminate") for node
// kinds whose width cannot be derived structurally (selects, member access,
// calls, casts, ...); callers treat 0 as "do not force-widen", so such an
// operand keeps its own evaluated width and the result is left unchanged.
static uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return LiteralWidth(expr->text, expr->int_val);
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;  // §5.7.1: one bit where self-determined
    case ExprKind::kIdentifier: {
      auto* var = ctx.FindVariable(expr->text);
      return var ? var->value.width : 0;
    }
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kBang || IsUnaryReductionOp(expr->op))
        return 1;
      return SimSelfWidth(expr->lhs, ctx);
    case ExprKind::kBinary:
      if (IsMaxWidthBinaryOp(expr->op))
        return std::max(SimSelfWidth(expr->lhs, ctx),
                        SimSelfWidth(expr->rhs, ctx));
      if (IsLeftWidthBinaryOp(expr->op)) return SimSelfWidth(expr->lhs, ctx);
      return 1;  // comparison / equality / logical -> one-bit result
    case ExprKind::kTernary:
      return std::max(SimSelfWidth(expr->true_expr, ctx),
                      SimSelfWidth(expr->false_expr, ctx));
    default:
      return 0;
  }
}

// §11.6.1: evaluate a binary operator's context-determined operands at the
// context width before combining them, so a wide sibling (or assignment
// context) keeps a narrow operand from truncating an intermediate carry --
// e.g. in `(a + b + 0) >> 1` the 32-bit literal 0 widens the addition's
// context to 32 bits, preserving a+b's carry into bit 16.
static Logic4Vec EvalContextDeterminedBinary(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             uint32_t context_width) {
  if (IsMaxWidthBinaryOp(expr->op)) {
    uint32_t w = std::max({context_width, SimSelfWidth(expr->lhs, ctx),
                           SimSelfWidth(expr->rhs, ctx)});
    return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena, w),
                        EvalExpr(expr->rhs, ctx, arena, w), arena,
                        context_width);
  }
  if (IsLeftWidthBinaryOp(expr->op)) {
    uint32_t w = std::max(context_width, SimSelfWidth(expr->lhs, ctx));
    return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena, w),
                        EvalExpr(expr->rhs, ctx, arena), arena, context_width);
  }
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena, context_width);
}

// §6.23 — the concrete type a single type_reference operand denotes at run
// time. A user class name (or `type(this)`, which stands for the class whose
// method is executing, §8.11) resolves to that class, whether it was written as
// a data type or as an expression; any other name resolves to a plain type
// name. `resolved` is false when the operand is not a type reference or names a
// class-less `this`.
struct TypeRefRuntimeId {
  std::string_view name;
  bool is_class = false;
  bool resolved = false;
};

static TypeRefRuntimeId ResolveTypeRefRuntimeId(const Expr* op,
                                                SimContext& ctx) {
  TypeRefRuntimeId id;
  if (!op || op->kind != ExprKind::kTypeRef) return id;
  if (op->lhs && op->lhs->kind == ExprKind::kIdentifier) {
    std::string_view name = op->lhs->text;
    if (name == "this") {
      // §6.23/§8.11: type(this) is the lexically enclosing class of the running
      // method, not the dynamic type of any handle.
      const ClassTypeInfo* cls = ctx.CurrentMethodClass();
      if (!cls) return id;
      id.name = cls->name;
      id.is_class = true;
      id.resolved = true;
      return id;
    }
    id.name = name;
    id.is_class = ctx.FindClassType(name) != nullptr;
    id.resolved = true;
    return id;
  }
  if (!op->text.empty()) {
    id.name = op->text;
    // A class name reaches here whenever it parses as a data type, which is
    // what `type(C)` does, while `type(this)` arrives through the expression
    // branch above. Both denote the same class, so both have to say so; asking
    // the same question of each is what lets the two forms compare equal.
    id.is_class = ctx.FindClassType(op->text) != nullptr;
    id.resolved = true;
  }
  return id;
}

// §6.23 — evaluate a comparison of two type references to a one-bit result:
// true exactly when the referenced types match (equality forms) or do not
// (inequality forms). Returns false, leaving `out` untouched, when `expr` is
// not an equality/inequality of two resolvable type references.
static bool TryTypeRefComparison(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  bool is_eq = expr->op == TokenKind::kEqEq || expr->op == TokenKind::kEqEqEq;
  bool is_neq =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  if (!is_eq && !is_neq) return false;
  if (!expr->lhs || expr->lhs->kind != ExprKind::kTypeRef) return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kTypeRef) return false;
  TypeRefRuntimeId a = ResolveTypeRefRuntimeId(expr->lhs, ctx);
  TypeRefRuntimeId b = ResolveTypeRefRuntimeId(expr->rhs, ctx);
  if (!a.resolved || !b.resolved) return false;
  bool matched = a.is_class == b.is_class && a.name == b.name;
  bool result = is_eq ? matched : !matched;
  out = MakeLogic4VecVal(arena, 1, result ? 1 : 0);
  return true;
}

static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width = 0) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  {
    Logic4Vec type_ref_result;
    if (TryTypeRefComparison(expr, ctx, arena, type_ref_result))
      return type_ref_result;
  }
  {
    Logic4Vec arr_result;
    if (TryArrayEqualityOp(expr, ctx, arena, arr_result)) return arr_result;
  }
  if (expr->op == TokenKind::kAmpAmp) return EvalLogicalAnd(expr, ctx, arena);

  if (expr->op == TokenKind::kAmpAmpAmp) {
    auto lv = EvalExpr(expr->lhs, ctx, arena);
    if (!lv.IsTruthy()) return MakeLogic4VecVal(arena, 1, 0);
    auto rv = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, rv.IsTruthy() ? 1 : 0);
  }
  if (expr->op == TokenKind::kPipePipe) return EvalLogicalOr(expr, ctx, arena);
  if (expr->op == TokenKind::kArrow) return EvalLogicalImpl(expr, ctx, arena);
  if (expr->op == TokenKind::kLtDashGt)
    return EvalLogicalEquiv(expr, ctx, arena);

  {
    Logic4Vec identity_result;
    if (TryEvalIdentityEquality(expr, ctx, arena, identity_result))
      return identity_result;
  }
  return EvalContextDeterminedBinary(expr, ctx, arena, context_width);
}

static Logic4Vec EvalTaggedExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width = 0) {
  if (expr->lhs) return EvalExpr(expr->lhs, ctx, arena, context_width);

  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalRealOrTimeLiteral(const Expr* expr, Arena& arena) {
  double v = expr->real_val;
  uint64_t bits = 0;
  std::memcpy(&bits, &v, sizeof(double));
  auto rv = MakeLogic4VecVal(arena, 64, bits);
  rv.is_real = true;
  return rv;
}

// §11.6.1: Table 11-21 sizes unary `+ - ~` by their operand and keeps only
// `!` and the reductions self-determined, so the operand of the three is
// context-determined and §11.8.2 propagates the expression's size down to it
// before the operator is applied, extending it by its sign where it is signed
// and by zero otherwise (§11.8.1). `logic [15:0] a = -8'd6` therefore negates
// the 16-bit 6 and reads fffa, as §5.7.1's final paragraph has a sized
// negative literal sign-extended into a wider logic object; negated at the
// literal's 8 bits and widened afterwards, it read 00fa. A real operand is
// not extended, and a context of 0 is a self-determined one.
static Logic4Vec EvalUnaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                               uint32_t context_width) {
  if (expr->op == TokenKind::kPlusPlus || expr->op == TokenKind::kMinusMinus) {
    return EvalPrefixUnary(expr, ctx, arena);
  }
  if (expr->op == TokenKind::kBang || IsUnaryReductionOp(expr->op) ||
      context_width == 0) {
    return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
  }
  uint32_t width = std::max(context_width, SimSelfWidth(expr->lhs, ctx));
  Logic4Vec operand = EvalExpr(expr->lhs, ctx, arena, width);
  if (!operand.is_real && operand.width < width)
    operand = ExtendVec(operand, width, operand.is_signed, arena);
  return EvalUnaryOp(expr->op, operand, arena);
}

static Logic4Vec EvalBinaryDispatch(const Expr* expr, SimContext& ctx,
                                    Arena& arena, uint32_t context_width) {
  if (IsCompoundAssignOp(expr->op)) {
    return EvalCompoundAssign(expr, ctx, arena);
  }
  if (expr->op == TokenKind::kKwMatches) {
    return EvalMatches(expr, ctx, arena);
  }
  return EvalBinaryExpr(expr, ctx, arena, context_width);
}

static Logic4Vec EvalMinTypMax(const Expr* expr, SimContext& ctx, Arena& arena,
                               uint32_t context_width) {
  DelayMode mode = ctx.GetDelayMode();
  Logic4Vec result;
  if (mode == DelayMode::kMin)
    result = EvalExpr(expr->lhs, ctx, arena, context_width);
  else if (mode == DelayMode::kMax)
    result = EvalExpr(expr->rhs, ctx, arena, context_width);
  else
    result = EvalExpr(expr->condition, ctx, arena, context_width);
  // Apply assignment-like context truncation (§10.8 mintymax expressions)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

Logic4Vec FillUnbasedUnsized(const Logic4Vec& v, uint32_t width, Arena& arena) {
  uint64_t af = (v.nwords > 0 && (v.words[0].aval & 1)) ? ~uint64_t{0} : 0;
  uint64_t bf = (v.nwords > 0 && (v.words[0].bval & 1)) ? ~uint64_t{0} : 0;
  auto out = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < out.nwords; ++w) {
    out.words[w].aval = af;
    out.words[w].bval = bf;
  }
  uint32_t rem = width % 64;
  if (rem != 0 && out.nwords > 0) {
    uint64_t mask = (uint64_t{1} << rem) - 1;
    out.words[out.nwords - 1].aval &= mask;
    out.words[out.nwords - 1].bval &= mask;
  }
  return out;
}

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  if (const auto* snap = ctx.FindDeferredArgSnapshot(expr)) {
    return *snap;
  }
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kUnbasedUnsizedLiteral: {
      auto v = EvalUnbasedUnsized(expr, arena);
      // §5.7.1: an unbased unsized literal takes the size of the context it
      // appears in, filling every bit with its single-bit value. Where no
      // context reaches it (context_width == 0) it is the 1-bit value that
      // fills whatever width it is later resized to.
      if (context_width == 0 || context_width == v.width) return v;
      return FillUnbasedUnsized(v, context_width, arena);
    }
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return EvalRealOrTimeLiteral(expr, arena);
    case ExprKind::kIdentifier:
      if (const Logic4Vec* bound = BoundInstanceValue(expr, ctx)) return *bound;
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      return EvalUnaryExpr(expr, ctx, arena, context_width);
    case ExprKind::kBinary:
      return EvalBinaryDispatch(expr, ctx, arena, context_width);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena, context_width);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalFunctionCall(expr, ctx, arena);
    case ExprKind::kPostfixUnary:
      return EvalPostfixUnary(expr, ctx, arena);
    case ExprKind::kMemberAccess:
      return EvalMemberAccessOrCall(expr, ctx, arena);
    case ExprKind::kCast:
      if (const Logic4Vec* bound = BoundInstanceValue(expr, ctx)) return *bound;
      return EvalCast(expr, ctx, arena);
    case ExprKind::kInside:
      return EvalInside(expr, ctx, arena);
    case ExprKind::kStreamingConcat:
      return EvalStreamingConcat(expr, ctx, arena);
    case ExprKind::kAssignmentPattern:
      return EvalAssignmentPattern(expr, ctx, arena);
    case ExprKind::kTagged:
      return EvalTaggedExpr(expr, ctx, arena, context_width);
    case ExprKind::kMinTypMax:
      return EvalMinTypMax(expr, ctx, arena, context_width);
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}  // namespace delta
