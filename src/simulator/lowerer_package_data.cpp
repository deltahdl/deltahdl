// §26.2 (printed page 808 of ~/LRM.pdf): the data items a package declares
// -- its variables and its parameters with initializers -- given storage
// ahead of every module under their "pk.name" keys, the key a `pk::name`
// reference and an import's alias resolve by, and their declaration
// assignments evaluated before any procedure starts, as the subclause
// requires. Moved out of lowerer_register.cpp, which registers a module's own
// declarations, once the package data outgrew it.

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

// The default a package variable with no initializer holds: §6.8's Table 6-7
// gives a 4-state integral variable x, which CreateVariable filled, and a
// 2-state one 0. A string and a real are registered as such, since a read of
// either goes through the kind rather than through the bits. §15.5 (printed
// page 378): a variable declared `event` is a named event, which `-> e`
// triggers, `@e` waits on and `e.triggered` reads, each through
// Variable::is_event as a module's is marked by LowerVar (lowerer_var.cpp);
// left clear, a package's `event e` was a one-bit value `-> p1::e` marked
// but nothing waited on or read as an event.
static void ShapePackageVariable(const ModuleItem* item, Variable* var,
                                 std::string_view qname, SimContext& ctx,
                                 Arena& arena) {
  const DataType& type = item->data_type;
  var->is_4state = DeclaredTypeIs4State(type);
  var->is_signed = DeclaredTypeIsSigned(type, ctx);
  var->value.is_signed = var->is_signed;
  if (!var->is_4state)
    var->value = MakeLogic4VecVal(arena, var->value.width, 0);
  var->is_event = type.kind == DataTypeKind::kEvent;
  if (DeclaredTypeIsString(type, ctx)) ctx.RegisterStringVariable(qname);
  bool is_real = type.kind == DataTypeKind::kReal ||
                 type.kind == DataTypeKind::kShortreal ||
                 type.kind == DataTypeKind::kRealtime;
  if (is_real) ctx.RegisterRealVariable(qname);
}

// The items of a package that declare data with storage of their own: every
// variable declaration, and a parameter with an initializer; any other item
// declares no data.
static bool DeclaresPackageData(const ModuleItem* item) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  return is_var || (is_param && item->init_expr);
}

// The "pk.name" key a package item's storage stands under, the one
// EvalMemberAccess reads a `pk::name` by.
static std::string PackageDataKey(const ModuleItem* item,
                                  std::string_view pkg) {
  return std::string(pkg) + "." + std::string(item->name);
}

// The width of a data item's storage: a variable's declared type's, and a
// parameter's, or a type no table sizes, 32 bits. §8.3 (printed page 180)
// with §8.4: a variable of a class type holds a handle to an object, which
// Lowerer::LowerVar sizes at 64 bits whatever the declaration's own width
// says (StorageWidth in lowerer_var.cpp); a package's is known to be one by
// the class record RegisterPackageClassVariables entered under `qname` ahead
// of this -- the package's own class, an imported one, or the built-in
// process or weak_reference class -- so its carrier is sized the same. Sized
// at 32, a handle written through `p1::h = new` was held in half its bits.
// An array of handles keeps its element width as before.
static uint32_t PackageDataWidth(const ModuleItem* item, std::string_view qname,
                                 SimContext& ctx) {
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  uint32_t width = is_var ? DeclaredTypeWidth(item->data_type, ctx) : 0;
  if (width != 0) return width;
  bool is_handle = is_var && item->unpacked_dims.empty() &&
                   !ctx.GetVariableClassType(qname).empty();
  return is_handle ? 64 : 32;
}

// §7.10 (printed page 169): N in `[$:N]` is a constant expression bounding
// the queue at N + 1 elements, and §11.2.1 lets it name a parameter, which
// for a package's queue is one of the package's own, read by its bare name
// through the frame a package subroutine's body runs in. `[$]` is unbounded,
// which CreateQueue spells -1, as is a bound the subclause rules out, which
// the elaborator has already reported.
static int32_t PackageQueueMaxSize(const Expr* dim, std::string_view pkg,
                                   SimContext& ctx, Arena& arena) {
  if (dim->rhs == nullptr) return -1;
  ctx.PushScope(pkg);
  auto bound = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  ctx.PopScope();
  std::optional<int32_t> size = QueueBoundMaxSize(bound);
  return size ? *size : -1;
}

// §7.4.2 (printed page 154): the bounds one unpacked dimension of a package
// array is declared with, `[l:r]` as written, either bound the greater, and
// `[size]` as [0:size-1]. Each bound is a constant expression, which §11.2.1
// lets name a parameter, for a package's array one of the package's own, so
// the caller has the package's frame pushed as PackageQueueMaxSize pushes it
// for a queue's bound. None for a dimension of neither form or a size that is
// not positive, which the elaborator has reported.
static std::optional<RtlirUnpackedDim> PackageArrayDim(const Expr* dim,
                                                       SimContext& ctx,
                                                       Arena& arena) {
  auto eval = [&](const Expr* e) {
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon)
    return RtlirUnpackedDim{eval(dim->lhs), eval(dim->rhs)};
  int64_t size = eval(dim);
  if (size <= 0) return std::nullopt;
  return RtlirUnpackedDim{0, size - 1};
}

// §7.4.2 with §7.4.4 (printed page 154): the unpacked extents of a package's
// fixed-size array, folded into `var` as the elaborator folds a module's
// (ComputeUnpackedDims and CollectUnpackedDimSizes in
// src/elaborator/elaborator_decls.cpp): every dimension's bounds in
// declaration order, the outermost summarized as the address the array
// counts from, its element count and its direction, and the per-dimension
// sizes CreateMultiDimLeaves reads for two dimensions or more. A package's
// items are not elaborated into RtlirVariables, so the fold is made here,
// in the package's frame. False where a dimension does not fold, which
// declares no array this can build.
static bool FoldPackageArrayDims(const ModuleItem* item, std::string_view pkg,
                                 RtlirVariable& var, SimContext& ctx,
                                 Arena& arena) {
  ctx.PushScope(pkg);
  bool folded = true;
  for (const Expr* dim : item->unpacked_dims) {
    std::optional<RtlirUnpackedDim> bounds =
        dim == nullptr ? std::nullopt : PackageArrayDim(dim, ctx, arena);
    if (!bounds) {
      folded = false;
      break;
    }
    var.unpacked_dims.push_back(*bounds);
    var.unpacked_dim_sizes.push_back(bounds->Size());
  }
  ctx.PopScope();
  if (!folded) return false;
  const RtlirUnpackedDim& outer = var.unpacked_dims.front();
  var.unpacked_lo = outer.Low();
  var.unpacked_size = outer.Size();
  var.is_descending = outer.left > outer.right;
  var.num_unpacked_dims = static_cast<uint32_t>(item->unpacked_dims.size());
  return true;
}

// §7.4.2 (printed page 154) with §26.2 (printed 808): a package variable
// declared with a fixed-size unpacked dimension is an array of elements, each
// storage of its own that an element select reads and writes and that
// foreach and $size count, so it is given the element variables and the
// ArrayInfo CreateArrayElements (lowerer_var.cpp) gives a module's, under the
// "pk.name" key its carrier variable stands under: "p1.a[1]" for the element
// and "p1.a" for the shape, the keys a bare `a[i]` inside the package's own
// subroutine resolves to (SimContext::FindInPackageScope and FindArrayInfo
// through ScopedObjectKeys). The carrier alone stood there, so `a[1] = 7` in
// a package function wrote bit 1 of a 32-bit carrier, `a[1]` read it back
// as one bit, and foreach ran once per bit of the carrier. CreateArrayElements
// reads the declaration as a RtlirVariable, so the item's type is shaped into
// one as ShapePackageVariable shapes the carrier, and its initializer
// (§7.4.2's assignment pattern, distributed by CreateArrayElements one item
// per element) is evaluated in the package's frame here rather than by
// InitPackageDataItem, which leaves the item alone.
static void CreatePackageArray(const ModuleItem* item, std::string_view pkg,
                               std::string_view qname, SimContext& ctx,
                               Arena& arena) {
  const DataType& type = item->data_type;
  RtlirVariable var;
  var.name = item->name;
  var.width = PackageDataWidth(item, qname, ctx);
  var.is_4state = DeclaredTypeIs4State(type);
  var.is_signed = DeclaredTypeIsSigned(type, ctx);
  var.is_string = DeclaredTypeIsString(type, ctx);
  var.is_real = type.kind == DataTypeKind::kReal ||
                type.kind == DataTypeKind::kShortreal ||
                type.kind == DataTypeKind::kRealtime;
  var.init_expr = item->init_expr;
  var.dtype = &type;
  var.elem_type_kind = type.kind;
  if (!FoldPackageArrayDims(item, pkg, var, ctx, arena)) return;
  ctx.PushScope(pkg);
  CreateArrayElements(qname, var, ctx, arena);
  ctx.PopScope();
}

// §7.5 (printed page 157) with §26.2 (printed 808): a package variable whose
// first unpacked dimension is `[]` is a dynamic array, sized by new[] or an
// array assignment and read by size(), which Lowerer::LowerVarAggregate
// (lowerer_var.cpp) backs for a module's with a QueueObject of no bound and
// an ArrayInfo marked dynamic; a package's is given both under its "pk.name"
// key. The carrier alone stood there, so `p1::d = new[3]` sized nothing,
// `p1::d[2] = 9` wrote nothing and `p1::d.size()` read 0.
static void CreatePackageDynArray(std::string_view qname, uint32_t width,
                                  bool is_4state, SimContext& ctx) {
  ctx.CreateQueue(qname, width, /*max_size=*/-1, is_4state);
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = width;
  info.is_4state = is_4state;
  ctx.RegisterArray(qname, info);
}

// §7.10 (printed page 169) and §7.8 (printed 163) with §26.2 (printed 808):
// a package variable declared with a queue dimension or an associative
// dimension is the queue or the associative array the methods and the
// element selects operate on, so it is given the QueueObject or the
// AssocArrayObject under the "pk.name" key its carrier variable stands
// under, as Lowerer::LowerVarAggregate (lowerer_var.cpp) gives a module's
// and CreateDeclAggregate (statement_assign_decl.cpp) a block's; a dynamic
// dimension (§7.5) and a fixed-size one (§7.4.2) are given their stores by
// the two functions above. The carrier alone stood there, so
// `p1::q.push_back(4)` and `p1::m["k"] = 5` found no object and did nothing,
// and a read of either element answered 0. The object is created outside
// every frame: SimContext::CreateQueue and CreateAssocArray keep one made
// inside a frame for that frame's life alone.
//
// §8.2 (printed page 179) with §7.10: a queue whose element type is a class
// holds handles, so `q[i].v` names a property of the object an element
// refers to (TryEvalQueueElementMember in eval_array_class_queue.cpp), which
// the queue is told by the flag LowerVarAggregate sets from the elaborated
// class name. The package's classes are lowered after its variables, so the
// class cannot be found by name here; the class record
// RegisterPackageClassVariables (lowerer_package_class_vars.cpp) entered
// under the item's own key ahead of this says the same. Left clear, the
// element `p1::q[0]` of a `C q[$]` was read as a value with no property.
static void CreatePackageAggregate(const ModuleItem* item, std::string_view pkg,
                                   std::string_view qname, SimContext& ctx,
                                   Arena& arena) {
  if (item->unpacked_dims.empty()) return;
  const Expr* dim = item->unpacked_dims.front();
  uint32_t width = PackageDataWidth(item, qname, ctx);
  bool is_4state = DeclaredTypeIs4State(item->data_type);
  if (dim == nullptr) {
    CreatePackageDynArray(qname, width, is_4state, ctx);
  } else if (IsQueueDim(dim)) {
    QueueObject* q = ctx.CreateQueue(
        qname, width, PackageQueueMaxSize(dim, pkg, ctx, arena), is_4state);
    q->holds_class_handles = !ctx.GetVariableClassType(qname).empty();
  } else if (item->unpacked_dims.size() == 1 && IsAssocIndexDim(dim, ctx)) {
    ctx.CreateAssocArray(qname, width, dim->text == "string",
                         AssocIndexSpec(dim, is_4state, ctx));
  } else {
    CreatePackageArray(item, pkg, qname, ctx, arena);
  }
}

// §15.3 (printed page 372): whether the package variable `item` is declared
// with the built-in semaphore class, which the parser leaves as a named type
// spelled `semaphore`, the spelling CreateSemaphoreForVar (lowerer_var.cpp)
// recognizes a module's by.
static bool IsPackageSemaphoreDecl(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kVarDecl &&
         item->data_type.kind == DataTypeKind::kNamed &&
         item->data_type.type_name == "semaphore";
}

// §15.3 (printed page 372) with §26.2 (printed 808): a package's `semaphore
// s` is the bucket of keys its get(), put() and try_get() operate on, made
// under the "pk.name" key its carrier variable stands under, as
// CreateSemaphoreForVar (lowerer_var.cpp) makes a module's, so that
// SemaphoreCallTarget (eval_semaphore.cpp) finds it by the key a `p1::s`
// receiver resolves to. §15.3.1 (printed 373): the declaration assignment is
// a new() whose one argument is the number of keys the bucket starts with,
// none when it is absent, and the argument is an expression of the package's
// scope, evaluated in the package's frame as PackageQueueMaxSize evaluates a
// queue's bound. A declaration with no initializer starts the bucket empty,
// as a module's does. The carrier alone stood there, the new() evaluated
// into it, so `p1::s.get()` and `p1::s.try_get()` ran on no semaphore.
static void CreatePackageSemaphore(const ModuleItem* item, std::string_view pkg,
                                   std::string_view qname, SimContext& ctx,
                                   Arena& arena) {
  SemaphoreObject* sem = ctx.CreateSemaphore(qname, 0);
  const Expr* init = item->init_expr;
  if (init == nullptr || init->kind != ExprKind::kCall || init->text != "new")
    return;
  ctx.PushScope(pkg);
  sem->key_count = SemaphoreKeyArg(init, ctx, arena, 0);
  ctx.PopScope();
}

// One package item's storage under its "pk.name" key: every variable
// declaration at its declared type's shape, with the semaphore, the queue or
// the associative array its type or dimension declares, and a parameter with
// an initializer as a 32-bit constant. The initializer is evaluated by
// InitPackageDataItem once every package's storage exists, except a
// semaphore's, which its bucket has already taken.
static void CreatePackageDataItem(const ModuleItem* item, std::string_view pkg,
                                  SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item)) return;
  auto* qname = arena.Create<std::string>(PackageDataKey(item, pkg));
  auto* var = ctx.CreateVariable(*qname, PackageDataWidth(item, *qname, ctx));
  if (item->kind != ModuleItemKind::kVarDecl) return;
  ShapePackageVariable(item, var, *qname, ctx, arena);
  if (IsPackageSemaphoreDecl(item)) {
    CreatePackageSemaphore(item, pkg, *qname, ctx, arena);
    return;
  }
  CreatePackageAggregate(item, pkg, *qname, ctx, arena);
}

void CreatePackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items)
      CreatePackageDataItem(item, pkg->name, ctx, arena);
  }
}

// §7.10 (printed page 169), §7.5.1 (printed 158) and §7.9.11 (printed 169)
// with §26.2 (printed 808): a package queue's or dynamic array's declaration
// assignment supplies its elements, `int q[$] = '{1, 2}` or `int d[] =
// new[3]`, and an associative array's its default and keyed entries, `int
// m[string] = '{default: 7}`, each landing in the object CreatePackageAggregate
// made under `key` through the helper a module's declaration goes through
// (InitQueueFromDeclInit and InitAssocFromDeclInit, lowerer_var.cpp). True
// where the key holds such an object, whose carrier variable the initializer
// must not reach: evaluated into the carrier, the pattern left the queue
// empty, so `p1::q.size()` read 0, and the array with no default, so
// `p1::m["x"]` read 0.
static bool InitPackageAggregate(const Expr* init, std::string_view key,
                                 SimContext& ctx, Arena& arena) {
  if (QueueObject* q = ctx.FindQueue(key)) {
    InitQueueFromDeclInit(q, init, ctx, arena);
    return true;
  }
  if (AssocArrayObject* aa = ctx.FindAssocArray(key)) {
    InitAssocFromDeclInit(init, aa, ctx, arena);
    return true;
  }
  return false;
}

// One package item's initializer, evaluated into the storage
// CreatePackageDataItem gave it; an item declaring no data, or none, has
// nothing to evaluate. §15.3.1: a semaphore's initializer is the new() that
// CreatePackageSemaphore has already read the bucket's key count from, and
// it names no value the carrier variable holds, so it is left alone, as is a
// fixed-size array's, which CreatePackageArray has already distributed over
// the elements (§7.4.2). A queue's, a dynamic array's or an associative
// array's fills the object (InitPackageAggregate); every other initializer
// is the carrier variable's value.
static void InitPackageDataItem(const ModuleItem* item, std::string_view pkg,
                                SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item) || item->init_expr == nullptr) return;
  if (IsPackageSemaphoreDecl(item)) return;
  std::string key = PackageDataKey(item, pkg);
  if (ctx.FindArrayInfo(key) != nullptr && ctx.FindQueue(key) == nullptr)
    return;
  if (InitPackageAggregate(item->init_expr, key, ctx, arena)) return;
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  if (found == variables.end()) return;
  found->second->value = EvalExpr(item->init_expr, ctx, arena);
}

void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  for (auto* pkg : design->packages) {
    // §26.2 with §26.3: the initializer is an expression of the package's
    // scope, reading the package's earlier variables, its subroutines and
    // those an import brings in by their bare names, which the frame a
    // package subroutine's body runs in resolves
    // (SimContext::FindInPackageScope and FindFunctionInPackageScope); the same
    // frame serves here. §26.6 (printed pages 815-816): a name an import
    // brings in through another package's export is the original
    // declaration, bound under the exporter's key by AliasPackageExports
    // (lowerer_import.cpp), which runs between CreatePackageDataVariables and
    // this so that p3's `int q = x` after `import p2::*` reads p1's x through
    // p2's `export p1::*`; evaluated ahead of the exports, it read 0.
    ctx.PushScope(pkg->name);
    for (auto* item : pkg->items)
      InitPackageDataItem(item, pkg->name, ctx, arena);
    ctx.PopScope();
  }
}

}  // namespace delta
