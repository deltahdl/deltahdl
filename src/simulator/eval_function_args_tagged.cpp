#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/virtual_interface.h"

namespace delta {

// §13.3 (printed page 337) declares a formal with any data_type, a structure
// or union written inline in the declaration among them. Such a type names
// no registered layout: RegisterDesignTypeLayouts registers a typedef's under
// the typedef's name and the lowerer a declaration's under the variable's, so
// the formal's is built from its DataType as RegisterAggregateLayout builds a
// declaration's, as wide as §7.2.1 (printed 147) makes the type, with a
// member naming a typedef of an aggregate of its own laid out through the
// nested type the elaborator resolved onto the declaration
// (ResolveFormalAggregateTypes in elaborator_items.cpp). The layout is built
// once and found again on every later call by its key, which names the
// declaration rather than the formal: the formal of another subroutine may
// share the name with a type of its own, and the layout table keys a module's
// variables by name as well, so the name alone would hand one subroutine's
// formal another's layout. The declaration's DataType stands at one address
// for the run, so the key is the formal's name with that address, and the
// registered layout's type_name is that key, owned by the arena. Empty where
// the formal's type writes no members.
static std::string_view InlineFormalLayoutKey(const FunctionArg& param,
                                              SimContext& ctx) {
  const DataType& dt = param.data_type;
  if (dt.struct_members.empty()) return {};
  std::string key =
      std::format("{}@{:x}", param.name, reinterpret_cast<uintptr_t>(&dt));
  if (const StructTypeInfo* info = ctx.FindStructType(key)) {
    return info->type_name;
  }
  Arena& arena = ctx.GetArena();
  auto* owned = arena.Create<std::string>(std::move(key));
  RegisterAggregateLayout(*owned, &dt, DeclaredTypeWidth(dt, ctx), ctx, arena);
  return *owned;
}

// §13.5.1 (printed page 348) copies the actual into a variable of the
// formal's type, and §11.9 (printed 304) has a tagged union expression's type
// known from its context -- for an actual, that formal. The key the formal's
// structure or union layout stands under in SimContext: the typedef's name
// where the formal is declared by one, which RegisterDesignTypeLayouts
// registers; the key InlineFormalLayoutKey registers the layout under where
// the aggregate is written inline in the formal's declaration. Without the
// latter `a.Valid` of an inline-typed formal was read through no member and
// `f(tagged Invalid)` raised nothing. Empty where the formal's type is
// neither.
static std::string_view FormalLayoutKey(const FunctionArg& param,
                                        SimContext& ctx) {
  const DataType& dt = param.data_type;
  if (!dt.type_name.empty() && ctx.FindStructType(dt.type_name) != nullptr)
    return dt.type_name;
  return InlineFormalLayoutKey(param, ctx);
}

// §11.9 (printed page 304): the braces of a tagged union expression are a
// §10.9.2 structure assignment pattern, and §10.9.2 (printed 263) evaluates
// each member expression in the context of an assignment to the member it
// initializes, by position or by name. An actual `f(tagged Add '{1, 2})` was
// evaluated as any expression is, with no type for the pattern to be placed
// by, so its elements were concatenated in written order at their
// self-determined widths -- `'{b: 2, a: 1}` swapped the members and
// `'{8'd1, 8'd2}` packed sixteen bits into the low end of the member. The
// pattern is evaluated against the layout of the member the expression names
// within the formal's union, exactly as EvalRhsWithStructContext evaluates
// the right-hand side of `u = tagged Add '{...}`. False where the actual is
// no tagged expression over a pattern, typed or bare, or the member has no
// layout of its own, so the actual is evaluated as it was.
static bool TryEvalTaggedPatternActual(const FunctionArg& param,
                                       const Expr* actual, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr ||
      actual->lhs == nullptr)
    return false;
  const Expr* pattern = UnwrapTypedPattern(actual->lhs);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  const StructTypeInfo* member =
      TaggedMemberLayout(*ctx.FindStructType(key), actual->rhs->text);
  if (member == nullptr) return false;
  out = EvalStructPatternValue(pattern, member, ctx, arena);
  return true;
}

// §10.9.2 (printed page 263): a structure assignment pattern evaluates each
// member expression in the context of an assignment to the member it
// initializes, by position or by name, and §13.5.1 (printed 348) makes the
// binding of an actual an assignment to a variable of the formal's type, so
// the structure the pattern is placed by is the formal's. An actual
// `f('{8'd1, 8'd2})` to `function int f(pair_t s)` was evaluated as any
// expression is, with no type to place it by, so its elements were
// concatenated in written order at their self-determined widths: the two
// bytes packed into the low end of the formal and `s.b` read 258, and
// `'{b: 2, a: 1}` swapped the members. The pattern, bare or typed, is
// evaluated against the formal's layout -- the typedef's or the inline one --
// as EvalRhsWithStructContext evaluates `s = '{...}`; a tagged expression
// over a pattern is placed by the member it names first. False where the
// actual is no pattern or the formal is no structure, so the actual is
// evaluated as it was. An element that is itself a pattern for a nested
// structure member is still evaluated untyped by EvalStructPatternValue.
bool TryEvalPatternActual(const FunctionArg& param, const Expr* actual,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalTaggedPatternActual(param, actual, ctx, arena, out)) return true;
  const Expr* pattern = UnwrapTypedPattern(actual);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  const StructTypeInfo* layout = ctx.FindStructType(key);
  if (layout->is_union) return false;
  out = EvalStructPatternValue(pattern, layout, ctx, arena);
  return true;
}

// §11.9 (printed page 303): a tagged union expression names a member and
// gives the value that tag, and (printed 304) its type is known from its
// context -- for an actual, the formal it is bound to, whose declared type
// names the union. §13.5.1 (printed 348) copies the value into the
// subroutine's own variable, and §7.3.2 (printed 151) has that value carry the
// tag beside the member's bits. RegisterValueArgStructType resolves the layout
// and the tag from an identifier actual's storage, which a tagged expression
// has none of, so `f(tagged Valid -7)` bound neither to the formal: `a.Valid`
// inside the body was read through no member and `f(tagged Invalid)` raised
// nothing. The layout is the one FormalLayoutKey names, bound as
// BindReturnStructLayout binds a return type's; the tag is the member the
// expression names. False where the actual is no tagged expression or the
// formal's type has no layout.
bool TryBindTaggedActual(const FunctionArg& param, const Expr* actual,
                         SimContext& ctx) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  ctx.SetVariableStructType(param.name, key);
  ctx.SetVariableTag(param.name, actual->rhs->text);
  return true;
}

// §13.5.1 (printed page 348) copies the actual into the subroutine's own
// variable, whose type is the formal's, and §7.2.1 (printed 147) makes a
// member read of that variable a window of the type's layout, whatever
// expression the value was copied from. RegisterValueArgStructType bound a
// formal's layout from an identifier actual's storage alone, and its fallback
// from a type name, which a structure or union written inline in the formal's
// declaration has none of: `f(g())` to `function int f(struct packed { int
// a, b; } s)` left the formal a plain vector and `s.a` in the body was read
// through no member. The formal's own type is laid out (InlineFormalLayoutKey)
// and bound under the formal's name, the key the body's reads ask by, before
// the actual is looked at, so an identifier's value and a computed one land
// in a laid-out formal alike. False for a formal whose type writes no
// members, which is bound as it was.
bool TryBindInlineAggregateFormal(const FunctionArg& param, SimContext& ctx) {
  std::string_view key = InlineFormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  ctx.SetVariableStructType(param.name, key);
  return true;
}

// §13.5.1 (printed page 348) copies the actual into a variable of the
// formal's type, and §7.2.1 (printed 147) makes a member read of that
// variable a window of the type's layout, whatever expression the value was
// copied from. A formal declared by a typedef's name was bound to a layout
// from an identifier actual's storage alone: `f('{1, 2})` and `f(g())` to
// `function int f(pair_t s)` left the formal a plain vector, so `s.a` in the
// body was read through no member, and `a.Valid` of a `u_t` formal given a
// call's result the same. The layout is the one RegisterDesignTypeLayouts
// registers under the typedef's name, bound as BindReturnStructLayout binds a
// return type's. False where the formal's type names no registered layout,
// which is bound as it was.
bool TryBindNamedAggregateFormal(const FunctionArg& param, SimContext& ctx) {
  std::string_view type_name = param.data_type.type_name;
  if (type_name.empty() || ctx.FindStructType(type_name) == nullptr)
    return false;
  ctx.SetVariableStructType(param.name, type_name);
  return true;
}

// The declared width BindValueArg, the default by-value bind, resizes the
// actual's value to before it creates the formal's variable. Computed using
// the live simulation scope, so a width that references in-scope
// (class/specialization) parameters -- e.g. `logic [W-1:0]` -- resolves to
// the bound parameter value instead of collapsing to 1 bit.
//
// A type carrying no packed dimension of its own is sized by DeclaredTypeWidth
// rather than the one-argument EvalTypeWidth, so that §6.18's user-defined type
// name contributes the width of the type it stands for. EvalTypeWidth gives a
// DataTypeKind::kNamed no width at all, and BindValueArg resizes only a
// non-zero width, so a formal written `nib p` was never resized and held
// whatever width the caller's expression happened to have: `8'hFF` passed to a
// four-bit formal read 255. §10.8 makes "the passing of a value to a subroutine
// input, output, or inout argument" an assignment-like context, so §10.7
// truncates or extends into the formal's declared width.
//
// A class-typed formal is passed the object handle (§8.2, printed page 180),
// so it holds a handle and is as wide as CreateFuncLocalVar makes a body
// local declared so, 64, rather than what the type table answers for the
// name.
// §8.27's forward declaration `typedef class C;` is the case that shows why
// the table is not asked: it records the name with no type behind it yet,
// which is DataTypeKind::kImplicit, and §6.10 makes that a scalar -- so the
// table holds 1 for the class, and resizing to it would leave one bit of a
// handle. The class is found as CreateFuncLocalVar finds it, by the key the
// run holds it under (DeclaredClassKey), `Outer::Inner` for a nested one.
// Answering no width at all left the formal as wide as the actual arrived,
// and the literal null arrives a bit wide, so `uvm_coreservice_t cs = null`
// bound from uvm_init(null) held one bit of the object `cs = dcs` stored:
// the null handle, and uvm_coreservice_t::get() then re-entered uvm_init
// without end.
uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx, Arena& arena) {
  if (!dt.packed_dim_left || !dt.packed_dim_right) {
    if (!DeclaredClassKey(dt, ctx, arena).empty()) return 64;
    // §25.9: a virtual interface formal, declared by the type or by a typedef
    // name standing for it, holds the handle of the instance it represents,
    // as wide as Lowerer::LowerVar makes a variable declared so, which is
    // what an output formal is sized to before the body assigns it.
    if (DeclaresAVirtualInterface(dt, ctx)) return 64;
    return DeclaredTypeWidth(dt, ctx);
  }
  auto span = [&](const Expr* l, const Expr* r) -> uint32_t {
    int64_t lv = static_cast<int64_t>(EvalExpr(l, ctx, arena).ToUint64());
    int64_t rv = static_cast<int64_t>(EvalExpr(r, ctx, arena).ToUint64());
    return static_cast<uint32_t>((lv >= rv ? lv - rv : rv - lv) + 1);
  };
  uint32_t width = span(dt.packed_dim_left, dt.packed_dim_right);
  for (const auto& [l, r] : dt.extra_packed_dims) width *= span(l, r);
  return width;
}

}  // namespace delta
