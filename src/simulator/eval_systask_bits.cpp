#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

// §8.25: the width of the type a type parameter of the running method's class
// is bound to on the object -- the actual of the object's specialization, or
// the default the class declares (§8.25.1) -- and 0 for a name that is no
// type parameter of that class, for a call outside a method, or for a type
// nothing sizes. The type table holds the class's default under the name, so
// the object is asked before it. A static method runs on no object: called
// through an explicit specialization, `Box#(byte)::bits()`, it reads the
// type the call's scope bound (§8.25.1, eval_class_scope_types.h), and
// through the default specialization the class's default; left to the
// expression, the name read the class's 32-bit parameter slot or the 1-bit
// local the value-parameter bind made of the type, whatever the type was.
static uint32_t BoundTypeParamWidth(std::string_view name, SimContext& ctx) {
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return ScopedTypeParamWidth(name, ctx);
  if (self->type == nullptr || self->type->decl == nullptr) return 0;
  const ClassDecl* decl = self->type->decl;
  std::string_view pname = TypeParamNamedBy(decl, name);
  if (pname.empty()) return 0;
  const DataType* actual = TypeParamActual(self, decl, pname);
  return actual != nullptr ? DeclaredTypeWidth(*actual, ctx) : 0;
}

// The bits of every element of the fixed-size unpacked array `arg` names --
// the array itself, or a sub-array of it that one index per dimension selects
// from the left, `m[1]` of `logic [7:0] m [2][3]` being three elements -- or 0
// where it names no such array.
// §20.6.2 with §23.6: the name of the array `arg` names -- an identifier's
// own, or the dotted path of a hierarchical reference such as u.mem naming an
// instance's array -- and empty where `arg` is neither.

static uint64_t FixedArrayBits(const Expr* arg, SimContext& ctx, Arena& arena) {
  size_t depth = 0;
  while (arg->kind == ExprKind::kSelect && arg->base != nullptr &&
         arg->index_end == nullptr) {
    arg = arg->base;
    ++depth;
  }
  std::string name = ArrayArgPath(arg, ctx, arena);
  if (name.empty()) return 0;
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue ||
      info->elem_type_kind == DataTypeKind::kString) {
    return 0;
  }
  std::vector<uint32_t> dims = info->dim_sizes;
  if (dims.empty()) dims.push_back(info->size);
  if (depth >= dims.size()) return 0;
  uint64_t count = 1;
  for (size_t d = depth; d < dims.size(); ++d) count *= dims[d];
  return count * info->elem_width;
}

// §8.23 and §26.3: the name a data type is written with through its class or
// package, `C::T`, `p::T` or `C::N::T`, as the type tables key it; empty where
// `arg` is not such a scope resolution of identifiers.
static std::string ScopedTypeName(const Expr* arg) {
  if (arg->kind == ExprKind::kIdentifier) return std::string(arg->text);
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution ||
      arg->lhs == nullptr || arg->rhs == nullptr ||
      arg->rhs->kind != ExprKind::kIdentifier)
    return {};
  std::string scope = ScopedTypeName(arg->lhs);
  if (scope.empty()) return {};
  return scope + "::" + std::string(arg->rhs->text);
}

// §20.6.2: the width of the data type `arg` names -- a type parameter bound
// on the running specialization, or a typedef by its bare name -- and, with
// §8.23 and §26.3, one named through its class or package, which read as an
// expression, `C::T`, was 1 bit. §8.25: through a specialization,
// `C#(shortint)::T`, the type is the one its list binds, where the table's
// "C::T" holds the declaration's default. 0 where `arg` names no type.

static uint64_t NamedTypeBits(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind == ExprKind::kIdentifier) {
    uint32_t tw = BoundTypeParamWidth(arg->text, ctx);
    return tw > 0 ? tw : TypedefBits(arg->text, ctx, arena);
  }
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution)
    return 0;
  if (uint32_t tw = SpecializationTypeParamWidth(arg, ctx, arena); tw > 0)
    return tw;
  std::string name = ScopedTypeName(arg);
  return name.empty() ? 0 : ctx.FindTypeWidth(name);
}

// §20.6.2 with §36.8.3: the width of the value a call of a system function
// an application registered returns, as its registration gives it, found
// without the call being made, since a calltf runs only when the function is
// executed; 0 where `arg` calls no registered system function.
static uint64_t UserSystemFunctionBits(const Expr* arg) {
  if (arg->kind != ExprKind::kSystemCall) return 0;
  VpiContext& vpi = GetGlobalVpiContext();
  const s_vpi_systf_data* data =
      vpi.ResolveSystf(std::string(arg->callee).c_str());
  if (data == nullptr || data->type != vpiSysFunc) return 0;
  const int kBits = vpi.SystfResultSizeBits(*data);
  return static_cast<uint64_t>(kBits > 0 ? kBits : kVpiDefaultSizedFuncBits);
}

Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);

  auto* arg = expr->args[0];
  // §20.6.2 (printed page 629): "the number of bits required to hold an
  // expression as a bit stream", which for a fixed-size unpacked array is
  // every element's bits -- 16 for `logic [7:0] m [0:1]`, of a net array as
  // of a variable one. Read as an expression the name is one element's worth,
  // so it is sized from the array's shape instead.
  if (uint64_t bits = FixedArrayBits(arg, ctx, arena); bits > 0) {
    return MakeLogic4VecVal(arena, 32, bits);
  }
  if (uint64_t tw = NamedTypeBits(arg, ctx, arena); tw > 0) {
    return MakeLogic4VecVal(arena, 32, tw);
  }
  // §20.6.2: the value "shall be determined without actual evaluation of the
  // expression it encloses", so a call of a function is sized by the type it
  // is declared to return and is not made.
  if (arg->kind == ExprKind::kCall) {
    SubroutineTarget target = FindSubroutineTarget(arg, ctx, arena);
    if (target.func != nullptr) {
      return MakeLogic4VecVal(arena, 32,
                              DeclaredTypeWidth(target.func->return_type, ctx));
    }
  }
  if (uint64_t bits = UserSystemFunctionBits(arg); bits > 0) {
    return MakeLogic4VecVal(arena, 32, bits);
  }
  // §20.6.2: a queue or dynamic array is a dynamically sized bit-stream
  // expression. Its current bit-stream size is the live element count times
  // the per-element width, so an empty one reports 0. Both kinds keep their
  // elements in a QueueObject, so this one lookup covers each, named bare or
  // hierarchically.
  if (std::string name = ArrayArgPath(arg, ctx, arena); !name.empty()) {
    if (auto* q = ctx.FindQueue(name)) {
      uint64_t bits = static_cast<uint64_t>(q->elements.size()) * q->elem_width;
      return MakeLogic4VecVal(arena, 32, bits);
    }
  }
  // §20.6.2 with §8.5: an unpacked array property of a class object holds its
  // elements one by one, and its bit stream is every element's, fixed-size or
  // dynamic, named bare in a method or through a handle.
  ClassArrayRef ref;
  if (ResolveClassArray(arg, ctx, arena, ref)) {
    return MakeLogic4VecVal(arena, 32,
                            static_cast<uint64_t>(ref.size) * ref.prop->width);
  }
  auto val = EvalExpr(arg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
}

}  // namespace delta
