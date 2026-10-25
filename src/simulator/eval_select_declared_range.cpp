// §11.5.1: the declared ranges a select of a value that carries no
// declaration of its own is resolved against -- a class property's, read off
// its member declaration, and a call's, read off the return type of the
// function it calls -- for SelectBaseRange in eval_select.cpp; and the packed
// dimension a select of a cast is resolved against, read off its casting
// type, for SelectBaseLevel there.

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// The member declaration of the property `name` in `type` or a class it
// extends, or null where none declares it.
static const ClassMember* DeclaringMember(const ClassTypeInfo* type,
                                          std::string_view name) {
  for (const ClassTypeInfo* c = type; c != nullptr; c = c->parent) {
    if (c->decl == nullptr) continue;
    for (const ClassMember* m : c->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == name) return m;
    }
  }
  return nullptr;
}

// The range the declared type `dt` writes with its one packed dimension, where
// that dimension spans a value `width` bits wide; none for any other type.
static std::optional<PackedRange> DeclaredTypeRange(const DataType& dt,
                                                    uint32_t width,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (dt.packed_dim_left == nullptr || dt.packed_dim_right == nullptr ||
      !dt.extra_packed_dims.empty())
    return std::nullopt;
  PackedRange range{
      SelectBoundValue(EvalExpr(dt.packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(dt.packed_dim_right, ctx, arena))};
  if (range.HighIndex() - range.LowIndex() + 1 != width) return std::nullopt;
  return range;
}

std::optional<PackedRange> PropertyDeclaredRange(const ClassTypeInfo* type,
                                                 std::string_view field,
                                                 uint32_t width,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  const ClassMember* m = DeclaringMember(type, field);
  if (m == nullptr) return std::nullopt;
  return DeclaredTypeRange(m->data_type, width, ctx, arena);
}

// §13.4.1: a call used as an implicit variable has the return type of the
// function it calls, and a select on it is resolved against that type's range
// (`get_val()[13:10]` on a `bit [15:10]` result).
std::optional<PackedRange> CalledFunctionRange(const Expr* base, uint32_t width,
                                               SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCall) return std::nullopt;
  const ModuleItem* func = ctx.FindFunction(base->callee);
  if (func == nullptr) return std::nullopt;
  return DeclaredTypeRange(func->return_type, width, ctx, arena);
}

// §16.8.1 (c): a reference to a sequence's formal bound to a variable_lvalue
// has the formal's type, and stands as a cast of the actual to that type
// (CastActualToFormal), so a select of it is resolved against the outermost
// packed dimension that type writes, each index of it an element as wide as
// the dimensions inside it make one (§7.4.4): the data type a type reference
// holds, or the declaration a typedef's name stands for.
std::optional<PackedLevel> CastTypeLevel(const Expr* base, uint32_t width,
                                         SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCast) return std::nullopt;
  const Expr* ref = base->rhs;
  const DataType* type = ref != nullptr && ref->kind == ExprKind::kTypeRef
                             ? ref->type_value
                             : ctx.FindTypeDeclaration(CastTypeKey(base, ctx));
  if (type == nullptr || type->packed_dim_left == nullptr) return std::nullopt;
  PackedRange range{
      SelectBoundValue(EvalExpr(type->packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(type->packed_dim_right, ctx, arena))};
  auto span = static_cast<uint32_t>(range.HighIndex() - range.LowIndex() + 1);
  return PackedLevel{range, width / span};
}

}  // namespace delta
