#include <algorithm>
#include <cmath>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
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
static bool IsAssocIndexDim(const Expr* dim, SimContext& ctx) {
  if (!dim || dim->kind != ExprKind::kIdentifier) return false;
  if (dim->text == "*") return true;
  if (TypeNameToDataType(dim->text).kind != DataTypeKind::kNamed) return true;
  if (ctx.FindClassType(dim->text) != nullptr) return true;
  return ctx.FindTypeWidth(dim->text) != 0;
}

// §7.4.2: "A fixed-size unpacked dimension may also be specified by a single
// positive constant integer expression to specify the number of elements in the
// unpacked dimension, as in C. In this case, [size] shall mean the same as
// [0:size-1]." The clause's own example gives `int Array[8][32]` and
// `int Array[0:7][0:31]` as the same declaration, so the size form is the
// ascending range counting from zero and is returned here as that range's upper
// bound.
//
// Every dimension is read this way, the clause's own `int Array[8][32]` being
// two of them. It was once restricted to a lone dimension because the range
// form beside it took the first of several and built one dimension from it, so
// admitting the size form would have spread that reading; the builder below now
// takes every dimension, and there is nothing left to spread.
//
// A queue dimension does not reach here: CreateBlockQueue is asked first and
// answers for every `[$]` and `[$:N]`.
static std::optional<int64_t> BlockArraySizeFormUpperBound(const Expr* dim,
                                                           SimContext& ctx,
                                                           Arena& arena) {
  if (IsAssocIndexDim(dim, ctx)) return std::nullopt;
  auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
  // §7.4.2 asks for a positive size. A declaration that gives anything else is
  // reported by the elaborator's ApplyConstSizedUnpackedDim, so nothing is
  // built here and the same rule is not named twice.
  if (size <= 0) return std::nullopt;
  return size - 1;
}

namespace {
// The bounds one unpacked dimension of a block declaration was written with,
// in the order it wrote them, so that a descending dimension stays
// distinguishable from the ascending one with the same address extent.
struct BlockDimBounds {
  int64_t left;
  int64_t right;
  int64_t Low() const { return std::min(left, right); }
  int64_t Count() const { return std::abs(left - right) + 1; }
};

// §7.4.2: bundle for materializing the leaves of a fixed multidimensional
// unpacked array declared in a block, keeping the recursive walk within the
// parameter-count limit -- the same reason lowerer_var.cpp's MultiDimArray
// exists for the declaration among a module's items.
struct BlockArrayLeaves {
  const std::vector<BlockDimBounds>& dims;
  uint32_t elem_width;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// The bounds of one dimension, evaluated against the running process. The two
// paths that build an unpacked array differ here and nowhere else: the lowerer
// reads what the elaborator folded, and a block declaration's dimensions are
// expressions the process evaluates as it reaches them.
static std::optional<BlockDimBounds> EvalBlockDim(const Expr* dim,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (!dim) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    return BlockDimBounds{
        static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64()),
        static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64())};
  }
  if (auto hi = BlockArraySizeFormUpperBound(dim, ctx, arena))
    return BlockDimBounds{0, *hi};
  return std::nullopt;
}

// §7.4.4 makes `int a[0:1][0:2]` an array of two arrays of three, and its
// leaves are named in row-major order by the address each dimension gives --
// §11.5.2 counting an address from the smaller of the two bounds the
// declaration wrote, whichever way round it wrote them. The names are the ones
// CreateMultiDimLeaves builds for a declaration among a module's items, because
// a leaf named `a[1][2]` by one path and anything else by the other would be
// read by neither: TryCompoundArraySelect looks the name up.
static void CreateBlockArrayLeaves(const BlockArrayLeaves& b, size_t d,
                                   const std::string& prefix) {
  if (d == b.dims.size()) {
    b.ctx.CreateVariable(*b.arena.Create<std::string>(prefix), b.elem_width);
    return;
  }
  int64_t low = b.dims[d].Low();
  for (int64_t i = 0; i < b.dims[d].Count(); ++i) {
    CreateBlockArrayLeaves(b, d + 1,
                           prefix + "[" + std::to_string(low + i) + "]");
  }
}

// §7.4.4: "A multidimensional array is an array of arrays. Multidimensional
// arrays can be declared by including multiple dimensions in a single
// declaration", and §7.4.2 has the dimensions following the identifier set the
// unpacked ones, so every one of them is one of the array's. This read the
// first and built the array as though the declaration had stopped there, so
// `int a[0:1][0:2]` in a begin-end block was two elements rather than six and a
// write to `a[1][2]` reached a leaf nothing had created. The declaration among
// a module's items builds all of them, and what the two paths must agree on --
// the leaf names, and the per-dimension extents $size, foreach and $readmemh
// read off dim_los/dim_sizes -- is what this now records as that one does.
static void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                                     SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  std::vector<BlockDimBounds> dims;
  dims.reserve(stmt->var_unpacked_dims.size());
  for (const auto* dim : stmt->var_unpacked_dims) {
    auto bounds = EvalBlockDim(dim, ctx, arena);
    // A dimension this cannot read is not one dimension missing but a shape
    // this function cannot build, so nothing is registered and nothing named.
    if (!bounds) return;
    dims.push_back(*bounds);
  }
  ArrayInfo info;
  // The lo/size pair keeps describing the outermost dimension, which is what
  // every whole-array and outer-index path reads, exactly as it does for the
  // declaration among a module's items.
  info.lo = static_cast<uint32_t>(dims[0].Low());
  info.size = static_cast<uint32_t>(dims[0].Count());
  info.elem_width = elem_width;
  info.is_descending = dims[0].left > dims[0].right;
  // Both are per-declaration facts the module path already records and this one
  // left at their defaults, so an `int` array declared in a block answered
  // 4-state and answered its element type as implicit.
  info.is_4state = DeclaredTypeIs4State(stmt->var_decl_type);
  info.elem_type_kind = stmt->var_decl_type.kind;
  if (dims.size() > 1) {
    for (const auto& dim : dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
      info.dim_sizes.push_back(static_cast<uint32_t>(dim.Count()));
      info.dim_descending.push_back(dim.left > dim.right);
    }
  }
  // §23.9: a declaration inside a begin-end block is local to that block, so
  // its shape goes away with the block rather than answering for a like-named
  // variable after it. The element variables below are created the same way a
  // few lines down in this file.
  ctx.RegisterArrayInScope(stmt->var_name, info);
  CreateBlockArrayLeaves(BlockArrayLeaves{dims, elem_width, ctx, arena}, 0,
                         std::string(stmt->var_name));
}

// §7.10: a declaration whose first unpacked dimension is `[$]` or `[$:N]`
// declares a queue, wherever the declaration stands. Creates the QueueObject
// the queue methods of §7.10.2 operate on, so that a declaration inside a
// procedural block gets the same backing store a declaration among a module's
// items gets from Lowerer::LowerVarAggregate. Returns true when it made one.
static bool CreateBlockQueue(const Stmt* stmt, uint32_t elem_width,
                             SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return false;
  const auto* dim = stmt->var_unpacked_dims[0];
  if (!IsQueueDim(dim)) return false;
  // §7.10.5: N in `[$:N]` bounds the queue at N + 1 elements, and `[$]` leaves
  // it unbounded, which CreateQueue spells -1. A bound the subclause rules out
  // is left unbounded here rather than reported: the elaborator's
  // CheckBlockQueueBounds already reports it, and a second report of one
  // declaration's one error would name the same rule twice.
  int32_t max_size = -1;
  if (dim->rhs) {
    auto bound =
        static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
    if (auto size = QueueBoundMaxSize(bound)) max_size = *size;
  }
  ctx.CreateQueue(stmt->var_name, elem_width, max_size,
                  Is4stateType(stmt->var_decl_type.kind));
  return true;
}

// §7.8 makes an associative array's dimension the type its index has, so a
// declaration written among a subroutine's statements builds one the way
// Lowerer::LowerVar (src/simulator/lowerer_var.cpp) builds one for a variable a
// module declares. Without it SimContext::CreateAssocArray was reached from
// that lowering and from an assoc-array formal argument and from nowhere else,
// so a local array existed for no name: ctx.FindAssocArray answered null, and
// TryAssocIndexedWrite, TryAssocCopyAssign and the read beside them each
// declined, storing nothing and reporting nothing (#3614).
//
// The index's own width and signedness are the index type's, taken from that
// type rather than from a table restated here -- §7.8's dimension is a
// data_type, and TypeNameToDataType with EvalTypeWidth and IsSignedType are
// what read one. A typedef'd index takes the width the elaborated table gives
// it, and a wildcard index takes neither: §7.8.4 leaves its value unsigned and
// self-determined, which is the default this spec carries.
//
// A packed dimension on the index -- §7.8's `int aa[bit[3:0]]`, whose index is
// four bits rather than one -- is not read here. That form reaches this path
// only in a subroutine, and the elaborator answers it for every module-level
// declaration; the width it would give is the product of the declared
// dimensions, which the dimension expression carries in its own elements.
static bool CreateBlockAssocArray(const Stmt* stmt, uint32_t elem_width,
                                  SimContext& ctx) {
  if (stmt->var_unpacked_dims.size() != 1) return false;
  const Expr* dim = stmt->var_unpacked_dims.front();
  if (!IsAssocIndexDim(dim, ctx)) return false;

  AssocArraySpec spec;
  spec.is_wildcard = dim->text == "*";
  spec.is_4state = DeclaredTypeIs4State(stmt->var_decl_type);
  DataType index_type = TypeNameToDataType(dim->text);
  if (index_type.kind != DataTypeKind::kNamed) {
    spec.index_width = EvalTypeWidth(index_type);
    spec.is_index_signed = IsSignedType(index_type, {});
  } else if (uint32_t named = ctx.FindTypeWidth(dim->text); named != 0) {
    spec.index_width = named;
  }
  // A.2.2.1 lets an integer type carry its own signing, and §7.8.4 keys an
  // entry off the index under it: the keys of a `byte unsigned` index order 0
  // to 255 rather than -128 to 127.
  if (dim->op == TokenKind::kKwUnsigned) spec.is_index_signed = false;
  if (dim->op == TokenKind::kKwSigned) spec.is_index_signed = true;
  ctx.CreateAssocArray(stmt->var_name, elem_width, dim->text == "string", spec);
  return true;
}

// §7.10 and §7.4.2: the storage a declaration's unpacked dimensions ask for
// beside the variable that carries one element's width. A queue dimension is
// not the range dimension of a fixed-size unpacked array, so a declaration is
// one or the other and never both.
//
// Both procedural declaration paths call this: a declaration outside a
// subroutine, which reaches CreateDeclVariable above, and one inside a
// subroutine body, which the function-body executor creates its local for. The
// two used to differ -- only the first made a queue -- so `int q[$];` written
// in a task body was a plain vector and q.push_back had no store to reach.
void CreateDeclAggregate(const Stmt* stmt, uint32_t elem_width, SimContext& ctx,
                         Arena& arena) {
  if (CreateBlockAssocArray(stmt, elem_width, ctx)) return;
  if (!CreateBlockQueue(stmt, elem_width, ctx, arena)) {
    CreateBlockArrayElements(stmt, elem_width, ctx, arena);
  }
}

static bool TryExecWeakRefVarDecl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->var_decl_type.type_name != "weak_reference") return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, "weak_reference");
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    exprs.reserve(type_params.size());
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init || stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new")
    return true;
  uint64_t referent = kNullClassHandle;
  if (!stmt->var_init->args.empty()) {
    auto val = EvalExpr(stmt->var_init->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
  return true;
}

// Records the class type-parameter override expressions (if any) for the
// just-created class variable `var_name`.
static void SetClassParamExprs(std::string_view var_name,
                               const std::vector<DataType>& type_params,
                               SimContext& ctx) {
  if (type_params.empty()) return;
  std::vector<Expr*> exprs;
  exprs.reserve(type_params.size());
  for (const auto& tp : type_params) {
    exprs.push_back(tp.type_ref_expr);
  }
  ctx.SetVariableClassParamExprs(var_name, std::move(exprs));
}

// Handles `T v = new src;` shallow-copy construction. Returns true if `init`
// names a copyable source object and the copy was installed into `var_name`.
static bool TryExecClassShallowCopy(std::string_view var_name, const Expr* init,
                                    SimContext& ctx, Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return false;
  auto src_val = EvalExpr(init->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
  return true;
}

static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  auto class_type = stmt->var_decl_type.type_name;
  if (class_type.empty() || !ctx.FindClassType(class_type)) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);

  SetClassParamExprs(stmt->var_name, stmt->var_decl_type.type_params, ctx);

  if (!stmt->var_init) return true;

  // §8.8: an argument-less typed constructor call (`C c = D::new;`) constructs
  // the specified type D, not the declared handle type C. It parses as a bare
  // scope-resolved member access, so it is not a `new` call and must be
  // dispatched before the generic expression path, which cannot construct it.
  {
    Logic4Vec typed;
    if (TryEvalTypedConstructorNew(stmt->var_init, ctx, arena, typed)) {
      auto* var = ctx.FindVariable(stmt->var_name);
      if (var) var->value = typed;
      return true;
    }
  }

  // A class-handle initializer that is not a `new` call (e.g. a copy from
  // another handle or a static call such as `process::self()`) is evaluated
  // and stored like an ordinary assignment; only `new` needs the
  // construction/shallow-copy handling below.
  if (stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new") {
    auto val = EvalExpr(stmt->var_init, ctx, arena);
    auto* var = ctx.FindVariable(stmt->var_name);
    if (var) var->value = val;
    return true;
  }

  if (TryExecClassShallowCopy(stmt->var_name, stmt->var_init, ctx, arena)) {
    return true;
  }

  auto handle = EvalClassNew(class_type, stmt->var_init, ctx, arena,
                             stmt->var_init->range.start);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->var_name, handle.ToUint64(), ctx, arena);
  return true;
}

static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  SimContext& ctx) {
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  if (width == 0 && DeclaredTypeIsString(stmt->var_decl_type, ctx)) {
    CreateVarInScope(stmt->var_name, 0, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    CreateVarInScope(stmt->var_name, width, ctx);
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    CreateDeclAggregate(stmt, width, ctx, arena);
  }
}

// §13.3.2: all variables of a static task are static. A local with no explicit
// lifetime keyword inherits its enclosing subroutine's lifetime, so a plain
// local declared inside a static-lifetime task/function is itself static and
// must be a single cell shared across every activation -- including concurrent
// ones. Such a local therefore has to resolve against the shared static-frame
// store rather than the per-activation scope stack (which, since automatic and
// block locals are now private to each process, would otherwise give each
// concurrent activation its own copy). An explicit `automatic` local never
// becomes static.
static bool IsEffectivelyStaticLocal(const Stmt* stmt,
                                     std::string_view func_name,
                                     SimContext& ctx) {
  if (stmt->var_is_static) return true;
  if (stmt->var_is_automatic || func_name.empty()) return false;
  auto* f = ctx.FindFunction(func_name);
  return f && f->is_static && !f->is_automatic;
}

// Returns true if the declaration resolves to an already-existing variable
// (a static-func var to alias, or a local already present) and so needs no
// fresh creation.
static bool TryReuseExistingDeclVar(const Stmt* stmt,
                                    std::string_view func_name,
                                    SimContext& ctx) {
  if (IsEffectivelyStaticLocal(stmt, func_name, ctx) && !func_name.empty()) {
    auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
    if (existing) {
      ctx.AliasLocalVariable(stmt->var_name, existing);
      return true;
    }
  } else if (!stmt->var_is_automatic) {
    if (ctx.HasLocalScope() && ctx.FindLocalVariable(stmt->var_name)) {
      return true;
    }
  }
  return false;
}

// §6.8's declared variable, as the declaration describes it rather than as the
// cell happens to have been created: the cell itself, the width the type asked
// for -- 0 where nothing could size it, which is not the carrier width
// CreateDeclVariable may have created the cell at -- and whether the type is
// one of the real family, whose initializer §6.12.1 converts rather than
// resizes. The three travel together because the initializer needs all of them
// to be assigned into the declared object rather than put in its place.
struct DeclaredObject {
  Variable* var;
  uint32_t declared_width;
  bool is_real;
};

// Applies 4-state coercion and the optional initializer to a freshly created
// variable, then records it as a static-func var when applicable.
//
// §6.8 executes a declaration's initializer "as if the assignment were made
// from an initial procedure", which §10.8 makes an assignment-like context, so
// §10.7 truncates or extends it into the width the declaration established. A
// Logic4Vec carries its own width, so writing the value straight over the
// variable put the expression's width in the declaration's place instead:
// `bit [3:0] v = 8'hFF;` in a procedural block left v eight bits reading 255.
// Lowerer::CoerceVarInitValue applies the same rule to a declaration at module
// scope and CreateFuncLocalVar to one in a subroutine body; a declaration in a
// procedural block runs here and had to be told it separately.
//
// The target is `declared_width`, the width the type asked for, rather than the
// width the variable was created at, and the two differ on exactly the cases
// this must leave alone. A type nothing could size is created at the 32-bit
// carrier CreateDeclVariable substitutes, and truncating to a carrier would cut
// a string reached through a typedef name (§6.16) down to the four characters
// 32 bits hold. A declared width of 0 says there is no width to resize to,
// which is what a string answers whether it is written bare or behind a name.
//
// A real is the one type whose created width is the target instead. §6.12.1
// converts an initializer that crosses the real/integer boundary rather than
// reinterpreting its bits, so `real r = 5;` has to hold the double 5.0; and
// `shortreal` declares 32 bits while being carried in the 64 that conversion
// needs. ConvertRealForKnownLhs performs the conversion, and resizes every
// value that does not cross the boundary.
//
// A declaration carrying an unpacked dimension is left as it was. Its variable
// is the element-width carrier that CreateBlockQueue and
// CreateBlockArrayElements size the real storage from rather than an object the
// initializer is assigned to, and `int a[3] = '{1,2,3}` evaluates to the
// ninety-six bits of a concatenation, which one element's width has nothing to
// say about.
static void InitializeDeclVariable(const Stmt* stmt, const DeclaredObject& obj,
                                   std::string_view func_name, SimContext& ctx,
                                   Arena& arena) {
  Variable* var = obj.var;
  var->is_4state = Is4stateType(stmt->var_decl_type.kind);
  if (!var->is_4state) CoerceTo2State(var->value);
  if (stmt->var_init) {
    Logic4Vec val = EvalExpr(stmt->var_init, ctx, arena);
    if (stmt->var_unpacked_dims.empty()) {
      uint32_t target = obj.is_real ? var->value.width : obj.declared_width;
      val = ConvertRealForKnownLhs(val, obj.is_real, target, arena);
    }
    var->value = val;
    if (!var->is_4state) CoerceTo2State(var->value);
  }

  if (IsEffectivelyStaticLocal(stmt, func_name, ctx) && !func_name.empty()) {
    ctx.SaveStaticFuncVar(func_name, stmt->var_name, var);
  }
}

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TryExecWeakRefVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;

  auto func_name = ctx.CurrentFuncName();
  if (TryReuseExistingDeclVar(stmt, func_name, ctx)) return StmtResult::kDone;

  // §6.18: a variable declared with a user-defined type name is an object of
  // the type that name stands for, so `nib v` is as wide as `nib` is.
  // DeclaredTypeWidth is what reaches that width, asking the elaborated typedef
  // table for a DataTypeKind::kNamed; the one-argument EvalTypeWidth gives such
  // a type no width at all, and CreateDeclVariable's `width == 0` fallback then
  // made every typedef'd local 32 bits. A type the table cannot size still
  // answers 0 and still reaches that fallback, and a string (§6.16) still
  // reaches the branch above it, because DeclaredTypeWidth answers 0 for a
  // string typedef as well as for a bare one.
  uint32_t width = DeclaredTypeWidth(stmt->var_decl_type, ctx);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  RecordVariableEnumType(stmt->var_name, stmt->var_decl_type, ctx);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    InitializeDeclVariable(stmt, {var, width, is_real}, func_name, ctx, arena);
  }
  return StmtResult::kDone;
}

}  // namespace delta
