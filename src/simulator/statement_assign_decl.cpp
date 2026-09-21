#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/virtual_interface.h"

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
  if (!dim || dim->kind != ExprKind::kIdentifier) return false;
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
// four bits rather than one -- is not read here. That form reaches this path
// only in a subroutine or a class, and the elaborator answers it for every
// module-level declaration; the width it would give is the product of the
// declared dimensions, which the dimension expression carries in its own
// elements.
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
  } else if (uint32_t named = ctx.FindTypeWidth(index_type.type_name);
             named != 0) {
    spec.index_width = named;
  }
  return spec;
}

AssocArraySpec AssocIndexSpec(const Expr* dim, bool elem_4state,
                              SimContext& ctx) {
  AssocArraySpec spec =
      AssocIndexSpecOfType(TypeNameToDataType(dim->text), elem_4state, ctx);
  spec.is_wildcard = dim->text == "*";
  // A.2.2.1 lets an integer type carry its own signing, and §7.8.4 keys an
  // entry off the index under it: the keys of a `byte unsigned` index order 0
  // to 255 rather than -128 to 127.
  if (dim->op == TokenKind::kKwUnsigned) spec.is_index_signed = false;
  if (dim->op == TokenKind::kKwSigned) spec.is_index_signed = true;
  return spec;
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

// §7.10 (printed page 169): whether the declaration's first unpacked
// dimension is a queue dimension, `[$]` or `[$:N]`.
static bool DeclaresQueue(const Stmt* stmt) {
  return !stmt->var_unpacked_dims.empty() &&
         IsQueueDim(stmt->var_unpacked_dims[0]);
}

// §7.10: a declaration whose first unpacked dimension is `[$]` or `[$:N]`
// declares a queue, wherever the declaration stands. Creates the QueueObject
// the queue methods of §7.10.2 operate on, so that a declaration inside a
// procedural block gets the same backing store a declaration among a module's
// items gets from Lowerer::LowerVarAggregate. Returns true when it made one.
static bool CreateBlockQueue(const Stmt* stmt, uint32_t elem_width,
                             SimContext& ctx, Arena& arena) {
  if (!DeclaresQueue(stmt)) return false;
  const auto* dim = stmt->var_unpacked_dims[0];
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
  auto* q = ctx.CreateQueue(stmt->var_name, elem_width, max_size,
                            Is4stateType(stmt->var_decl_type.kind));
  // §8.4 (printed page 181): a queue of a class type holds handles, so
  // `q[i].v` names a property of the object an element refers to
  // (TryEvalQueueElementMember in eval_array_class_queue.h). §8.23 (printed
  // 200-201): the class is looked for under the declaration's spelling,
  // `Outer::Inner` for a nested class (DeclaredClassKey); by the bare
  // `Inner` alone, `Outer::Inner q[$]` was a queue of plain values.
  q->holds_class_handles =
      !DeclaredClassKey(stmt->var_decl_type, ctx, arena).empty();
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
static bool CreateBlockAssocArray(const Stmt* stmt, uint32_t elem_width,
                                  SimContext& ctx) {
  if (stmt->var_unpacked_dims.size() != 1) return false;
  const Expr* dim = stmt->var_unpacked_dims.front();
  if (!IsAssocIndexDim(dim, ctx)) return false;
  ctx.CreateAssocArray(
      stmt->var_name, elem_width, dim->text == "string",
      AssocIndexSpec(dim, DeclaredTypeIs4State(stmt->var_decl_type), ctx));
  return true;
}

// §7.5 (printed pages 157-158): a declaration whose first unpacked dimension
// is `[]`, which the parser records as a null dimension, declares a dynamic
// array, empty until new[] sizes it (§7.5.1), wherever the declaration
// stands. It is given what Lowerer::LowerVarAggregate (lowerer_var.cpp) gives
// a module's and CreatePackageDynArray (lowerer_package_data.cpp) a
// package's: the unbounded QueueObject `d = new[3]`, `d[1] = 5` and
// `d.size()` operate on, and the ArrayInfo marked dynamic that the
// whole-array reads and writes consult, the latter registered for the
// block's life as a fixed-size array's shape is. Before this the null
// dimension reached CreateBlockArrayElements, which reads no bounds off it
// and built nothing, so a block's or a subroutine body's `int d[]` had no
// store: new[] sized nothing and the element read 0.
//
// §7.5.1 (printed 158): the new[] constructor may stand as the declaration
// assignment's right-hand side, sizing the array and copying the optional
// initialization array, as Lowerer::LowerDynArrayNewInit does for a module's
// `int d[] = new[3]`. A block's initializer was evaluated onto the carrier
// variable alone -- InitializeDeclVariable below and CreateFuncLocalVar
// (eval_function_body.cpp) treat every initializer of a declaration with
// unpacked dimensions so -- and the array stayed empty, `d.size()` reading 0.
// The initializer is run as the assignment `d = new[3]` it stands for
// (§6.8), through the new[] arm of TryQueueBlockingAssign, which sizes,
// default-initializes and copies as the executed statement does.
static void SizeBlockDynArrayFromInit(const Stmt* stmt, Arena& arena,
                                      SimContext& ctx) {
  const Expr* init = stmt->var_init;
  if (init == nullptr || init->kind != ExprKind::kCall || init->text != "new" ||
      init->args.empty()) {
    return;
  }
  auto* target = arena.Create<Expr>();
  target->kind = ExprKind::kIdentifier;
  target->range = stmt->range;
  target->text = stmt->var_name;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->range = stmt->range;
  assign->lhs = target;
  assign->rhs = stmt->var_init;
  TryQueueBlockingAssign(assign, ctx, arena);
}

static bool CreateBlockDynArray(const Stmt* stmt, uint32_t elem_width,
                                SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty() || stmt->var_unpacked_dims[0] != nullptr)
    return false;
  bool is_4state = DeclaredTypeIs4State(stmt->var_decl_type);
  ctx.CreateQueue(stmt->var_name, elem_width, /*max_size=*/-1, is_4state);
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = elem_width;
  info.is_4state = is_4state;
  ctx.RegisterArrayInScope(stmt->var_name, info);
  SizeBlockDynArrayFromInit(stmt, arena, ctx);
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
  if (CreateBlockDynArray(stmt, elem_width, ctx, arena)) return;
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

void RecordClassParamActuals(std::string_view var_name,
                             const std::vector<DataType>& type_params,
                             SimContext& ctx) {
  if (type_params.empty()) return;
  std::vector<Expr*> exprs;
  exprs.reserve(type_params.size());
  for (const auto& tp : type_params) {
    exprs.push_back(tp.type_ref_expr);
  }
  ctx.SetVariableClassParamExprs(var_name, std::move(exprs));
  ctx.RegisterVariableClassTypeParams(var_name, &type_params);
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

// §8.23 (printed pages 200-201 of ~/LRM.pdf): a procedural `Outer::Inner i =
// new;` names the nested class by its scoped spelling, which DeclaredClassKey
// (declared_class_key.h) resolves to the key the run holds it under; looked up
// by the bare `Inner` alone, the declaration found no class, became a plain
// variable, and `i.take()` ran nothing.
//
// §7.10 (printed 169), §7.4.2 (printed 153-154), §7.5 (printed 157) and §7.8
// (printed 163) with §8.4 (printed 181): `C q[$]`, `C arr[2]`, `C d[]` and
// `C aa[string]` declare a queue or an array whose elements are handles, not
// a handle, so a declaration with an unpacked dimension is left to
// ExecVarDeclImpl's aggregate path, which builds the queue or the array
// (CreateDeclAggregate) as Lowerer::LowerVar builds a module's. Taken here,
// each became one scalar handle under the array's name: `q.push_back(i)`
// found no queue, `aa["k"] = new` no array, and `arr[0] = b` set a bit of
// the handle.
static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  if (!stmt->var_unpacked_dims.empty()) return false;
  std::string_view class_type =
      DeclaredClassKey(stmt->var_decl_type, ctx, arena);
  if (class_type.empty()) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);

  RecordClassParamActuals(stmt->var_name, stmt->var_decl_type.type_params, ctx);

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

// §6.11.3: a declaration in a procedural block or a task body carries its
// declared signedness as a module-scope declaration does (Lowerer sets the
// same flag there) and as a subroutine body local does (CreateFuncLocalVar),
// so an `int` declared in a task is a signed operand, and a solver drawing
// it (18.12) draws it over the signed range rather than the unsigned one.
static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  bool is_signed, SimContext& ctx) {
  if (ctx.HasLocalScope())
    return ctx.CreateLocalVariable(name, width, is_signed);
  Variable* var = ctx.CreateVariable(name, width);
  var->is_signed = is_signed;
  var->value.is_signed = is_signed;
  return var;
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  bool is_signed = DeclaredTypeIsSigned(stmt->var_decl_type, ctx);
  if (width == 0 && DeclaredTypeIsString(stmt->var_decl_type, ctx)) {
    CreateVarInScope(stmt->var_name, 0, is_signed, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    Variable* var = CreateVarInScope(stmt->var_name, width, is_signed, ctx);
    // §6.12: marked on the variable as well as registered by name, so a
    // reader holding the variable and one holding the name answer alike.
    var->is_real = is_real;
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

// The static frame a static local lives in: its subroutine's, or, for a
// declaration written static outside any subroutine, a frame of the
// declaration's own named after where it is written. §6.21 makes such a
// variable one cell for the whole simulation, shared by every activation of
// the block that declares it, and §18.17 puts one in the code block of a
// randsequence, an anonymous automatic scope that is pushed afresh for every
// activation and so cannot keep the cell itself. The name is arena-persisted
// because the frame store keys on string_view.
static std::string_view StaticFrameOf(const Stmt* stmt,
                                      std::string_view func_name,
                                      SimContext& ctx) {
  if (!func_name.empty()) return func_name;
  auto* key = ctx.GetArena().Create<std::string>(
      std::format("static@{}:{}:{}", stmt->range.start.file_id,
                  stmt->range.start.line, stmt->range.start.column));
  return *key;
}

// Returns true if the declaration resolves to an already-existing variable
// (a static var to alias, or a local already present) and so needs no fresh
// creation.
static bool TryReuseExistingDeclVar(const Stmt* stmt,
                                    std::string_view func_name,
                                    SimContext& ctx) {
  if (IsEffectivelyStaticLocal(stmt, func_name, ctx)) {
    auto* existing = ctx.FindStaticFuncVar(StaticFrameOf(stmt, func_name, ctx),
                                           stmt->var_name);
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
// variable, then records it in its static frame when it is static.
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
  // §6.8 (Table 6-7): a 4-state local starts as 'x whatever the scope's
  // lifetime, as a module's does (§13.3, §13.4). A local of an automatic
  // task or block is made by SimContext::CreateLocalVariable, which fills it
  // with 0 where CreateVariable fills a module's with x, so `logic l;` in an
  // automatic task read 0. A virtual interface keeps the null handle set
  // above, and a declaration with unpacked dimensions is the element-width
  // carrier its elements are sized from rather than a value.
  if (var->is_4state && !var->is_virtual_interface && !stmt->var_init &&
      stmt->var_unpacked_dims.empty() && var->value.width > 0) {
    var->value = MakeAllX(arena, var->value.width);
    var->value.is_signed = var->is_signed;
  }
  if (stmt->var_init) {
    Logic4Vec val = EvalExpr(stmt->var_init, ctx, arena);
    if (stmt->var_unpacked_dims.empty()) {
      uint32_t target = obj.is_real ? var->value.width : obj.declared_width;
      val = ConvertRealForKnownLhs(val, obj.is_real, target, arena);
    }
    var->value = val;
    if (!var->is_4state) CoerceTo2State(var->value);
  }

  if (IsEffectivelyStaticLocal(stmt, func_name, ctx)) {
    ctx.SaveStaticFuncVar(StaticFrameOf(stmt, func_name, ctx), stmt->var_name,
                          var);
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
  //
  // §25.9: a virtual interface declared in a task body or a begin-end block,
  // by the type or by a typedef name standing for it, holds the handle of the
  // instance it represents, as wide as Lowerer::LowerVar makes a variable
  // declared so and as CreateFuncLocalVar makes a function-body local
  // declared so, and is flagged so that a member the block reaches through
  // it, `v.clk` after `v = dif`, is a component of that instance
  // (ResolveVirtualInterfaceBase). It holds the null handle
  // before it is initialized, as the clause says and as Lowerer::LowerVar
  // sets, rather than the x a 4-state declaration starts at. DeclaredTypeWidth
  // answers 0 for the type, so before this such a local took the 32-bit
  // carrier and no reader took it for a virtual interface.
  //
  // §8.4 (printed page 181): a queue or an array of a class type, which
  // TryExecClassVarDecl leaves to this path, carries one handle per element,
  // as wide as a handle variable is made (64), where DeclaredTypeWidth
  // answers 0 for a class and the carrier below would have sized the elements
  // at 32; and the class is recorded under the array's name as
  // Lowerer::LowerVar records a module's (SetVariableClassType), which is
  // what tells an associative array of handles from one of values when
  // `aa["k"] = new` constructs into an entry and `aa["k"].v` reads through
  // one (HandleArrayOfSelect in eval_assoc_class_handles.cpp).
  bool is_virtual_interface =
      DeclaresAVirtualInterface(stmt->var_decl_type, ctx);
  std::string_view class_key =
      DeclaredClassKey(stmt->var_decl_type, ctx, arena);
  bool is_class = !class_key.empty();
  uint32_t width = is_virtual_interface || is_class
                       ? 64
                       : DeclaredTypeWidth(stmt->var_decl_type, ctx);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  RecordVariableEnumType(stmt->var_name, stmt->var_decl_type, ctx);
  if (is_class) ctx.SetVariableClassType(stmt->var_name, class_key);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    var->is_virtual_interface = is_virtual_interface;
    if (is_virtual_interface) var->value = MakeLogic4VecVal(arena, width, 0);
    // §11.5.1: which bit an index of this variable addresses is decided by
    // its declaration, and a declaration here recorded no range at all: a
    // `bit [15:10] v` in a procedure was addressed as [5:0], and so was a
    // `Node::value_t v` standing for it (§6.18), whose `v[13:10]` then read
    // four bits outside a six-bit vector -- x, and 0 once assigned to a
    // 2-state target (#3808). Lowerer::LowerVar records a module-scope
    // declaration's range; this is the same fact for a procedure's.
    if (!is_virtual_interface)
      RecordDeclaredRange(stmt->var_decl_type, var, ctx, arena);
    InitializeDeclVariable(stmt, {var, width, is_real}, func_name, ctx, arena);
  }
  return StmtResult::kDone;
}

}  // namespace delta
