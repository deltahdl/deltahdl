#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

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

// §11.9 (printed page 304): a tagged union expression's type is known from
// its context -- for an actual, the formal it is bound to. The key the
// formal's union layout stands under in SimContext: the typedef's name where
// the formal is declared by one, which RegisterDesignTypeLayouts registers;
// the key InlineFormalLayoutKey registers the layout under where the union is
// written inline in the formal's declaration. Without the latter `a.Valid` of
// an inline-typed formal was read through no member and `f(tagged Invalid)`
// raised nothing. Empty where the formal's type is neither.
static std::string_view FormalUnionLayoutKey(const FunctionArg& param,
                                             SimContext& ctx) {
  const DataType& dt = param.data_type;
  if (!dt.type_name.empty() && ctx.FindStructType(dt.type_name) != nullptr)
    return dt.type_name;
  return InlineFormalLayoutKey(param, ctx);
}

// §11.9: the struct layout of the union member a tagged expression names, or
// null when the union declares no such member with a layout of its own. The
// assignment statement's copy stands in statement_assign_core.cpp.
static const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                                std::string_view member) {
  for (const auto& field : sinfo.fields) {
    if (field.name == member && field.nested) return field.nested;
  }
  return nullptr;
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
bool TryEvalTaggedPatternActual(const FunctionArg& param, const Expr* actual,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr ||
      actual->lhs == nullptr)
    return false;
  const Expr* pattern = UnwrapTypedPattern(actual->lhs);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string_view key = FormalUnionLayoutKey(param, ctx);
  if (key.empty()) return false;
  const StructTypeInfo* member =
      TaggedMemberLayout(*ctx.FindStructType(key), actual->rhs->text);
  if (member == nullptr) return false;
  out = EvalStructPatternValue(pattern, member, ctx, arena);
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
// nothing. The layout is the one FormalUnionLayoutKey names, bound as
// BindReturnStructLayout binds a return type's; the tag is the member the
// expression names. False where the actual is no tagged expression or the
// formal's type has no layout.
bool TryBindTaggedActual(const FunctionArg& param, const Expr* actual,
                         SimContext& ctx) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr) return false;
  std::string_view key = FormalUnionLayoutKey(param, ctx);
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

}  // namespace delta
