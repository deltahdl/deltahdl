#include <cstdint>
#include <cstdlib>

#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// §7.8 writes an associative array's dimension as the type its index has, and
// §7.8.1 writes the wildcard index as `*`. The parser records both as an
// identifier naming the type, which is the shape §7.4.2's size form also has
// when the size is a parameter, so the two are told apart by what the name
// means rather than by how the dimension is written: an index type is a
// keyword, the wildcard, a class, or a name the elaborated typedef table
// answers for, and a size is anything else.
//
// A name the table answers 0 for is read as a size. That is the string typedef
// of #3486, which the table cannot distinguish from a type it never saw; an
// associative array keyed by one builds nothing either way, since evaluating a
// type name as an expression yields no size, so the reading costs nothing that
// was working.
//
// A class property's dimension is the same dimension (§8.5 puts no restriction
// on a property's type), so eval_array_class_assoc.cpp asks this of one too.
bool IsAssocIndexDim(const Expr* dim, SimContext& ctx) {
  if (!dim) return false;
  // A.2.5: an index written as a data_type no expression can spell, or as a
  // type reference, is kept as a type reference, which no size is.
  if (dim->kind == ExprKind::kTypeRef) return true;
  if (dim->kind != ExprKind::kIdentifier) return false;
  if (dim->text == "*") return true;
  if (TypeNameToDataType(dim->text).kind != DataTypeKind::kNamed) return true;
  if (ctx.FindClassType(dim->text) != nullptr) return true;
  return ctx.FindTypeWidth(dim->text) != 0;
}

// The index's own width and signedness are the index type's, taken from that
// type rather than from a table restated here -- §7.8's dimension is a
// data_type, and TypeNameToDataType with EvalTypeWidth and IsSignedType are
// what read one. A typedef'd index takes the width the elaborated table gives
// it, and a wildcard index takes neither: §7.8.4 leaves its value unsigned and
// self-determined, which is the default this spec carries.
//
// A packed dimension on the index -- §7.8's `int aa[bit[3:0]]`, whose index is
// four bits rather than one -- is read by AssocIndexSpec, from the dimension
// expression's own elements.
AssocArraySpec AssocIndexSpecOfType(const DataType& index_type,
                                    bool elem_4state, SimContext& ctx) {
  AssocArraySpec spec;
  spec.is_4state = elem_4state;
  if (index_type.kind != DataTypeKind::kNamed) {
    // A string has no width to key by (§7.8.2 keys it by value), so it keeps
    // the default rather than the 0 EvalTypeWidth answers for it.
    if (uint32_t width = EvalTypeWidth(index_type); width != 0)
      spec.index_width = width;
    spec.is_index_signed = IsSignedType(index_type, {});
  } else if (ctx.FindClassType(index_type.type_name) != nullptr) {
    // §7.8.3: a class index keys by handle, which the run holds in 64 bits,
    // as the elaborator sizes a declared array's class index.
    spec.index_width = 64;
    spec.index_class = index_type.type_name;
  } else {
    // §12.7.3: a foreach over the array gives its loop variable the type the
    // name stands for, an enumeration's included (index_type_name).
    spec.index_type_name = index_type.type_name;
    if (uint32_t named = ctx.FindTypeWidth(index_type.type_name); named != 0)
      spec.index_width = named;
  }
  return spec;
}

DataType AssocIndexType(const Expr* dim) {
  if (dim->kind == ExprKind::kTypeRef) return *dim->type_value;
  return TypeNameToDataType(dim->text);
}

bool IsStringIndexDim(const Expr* dim) {
  return AssocIndexType(dim).kind == DataTypeKind::kString;
}

AssocArraySpec AssocIndexSpec(const Expr* dim, bool elem_4state,
                              SimContext& ctx) {
  AssocArraySpec spec =
      AssocIndexSpecOfType(AssocIndexType(dim), elem_4state, ctx);
  spec.is_wildcard = dim->text == "*";
  // A.2.2.1 lets an integer type carry its own signing, and §7.8.4 keys an
  // entry off the index under it: the keys of a `byte unsigned` index order 0
  // to 255 rather than -128 to 127.
  if (dim->op == TokenKind::kKwUnsigned) spec.is_index_signed = false;
  if (dim->op == TokenKind::kKwSigned) spec.is_index_signed = true;
  // §7.8 with A.2.2.1: an integer_vector_type index carries its packed
  // dimensions, `[bit [79:0]]` keying by 80 bits rather than one, the width
  // the product of the dimensions' sizes as the elaborator gives a
  // module-level declaration's; a class property's and a subroutine's reach
  // the run unanswered.
  if (!dim->elements.empty()) {
    uint32_t width = 1;
    for (const Expr* packed : dim->elements) {
      auto msb = static_cast<int64_t>(
          EvalExpr(packed->lhs, ctx, ctx.GetArena()).ToUint64());
      auto lsb = static_cast<int64_t>(
          EvalExpr(packed->rhs, ctx, ctx.GetArena()).ToUint64());
      width *= static_cast<uint32_t>(std::abs(msb - lsb) + 1);
    }
    spec.index_width = width;
  }
  return spec;
}

}  // namespace delta
