// §26.2 (printed page 808 of ~/LRM.pdf) with §3.12.1 (printed 56): the data
// items a package and the compilation-unit scope declare -- their variables
// and their parameters with initializers -- given storage ahead of every
// module, and their declaration assignments evaluated before any procedure
// starts, as the two subclauses require. A package's item stands under its
// "pk.name" key, the key a `pk::name` reference and an import's alias resolve
// by, and the compilation unit's under its "$unit.name" key, which each
// module's bare reference is bound to under the module's own prefix
// (AliasUnitDataItems) unless the module declares the name. Moved out of
// lowerer_register.cpp, which registers a module's own declarations, once
// the two scopes' data outgrew it.

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sync_objects.h"
#include "simulator/sync_variable.h"
#include "simulator/variable.h"

namespace delta {

// §15.3 (printed page 372) and §15.4 (printed 374): the built-in
// synchronization class the package variable `item` is declared with,
// `semaphore` or `mailbox`, which the parser leaves as a named type of that
// spelling, the spelling CreateSyncObjectForVar (sync_variable.cpp)
// recognizes a module's by. Empty for an item of any other
// type.
static std::string_view PackageSyncObjectType(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kVarDecl ||
      item->data_type.kind != DataTypeKind::kNamed)
    return {};
  std::string_view name = item->data_type.type_name;
  if (name == "semaphore" || name == "mailbox") return name;
  return {};
}

// §8.3 (printed page 180) with §8.4 (printed 181-182): whether the package
// item declares a handle -- a variable of a class the record
// RegisterPackageClassVariables (lowerer_register.cpp) entered under `qname`
// ahead of this names, or of the built-in semaphore or mailbox class, which
// has no record and is known by its spelling (PackageSyncObjectType).
static bool PackageItemIsHandle(const ModuleItem* item, std::string_view qname,
                                SimContext& ctx) {
  if (item->kind != ModuleItemKind::kVarDecl) return false;
  return !ctx.GetVariableClassType(qname).empty() ||
         !PackageSyncObjectType(item).empty();
}

// The default a package variable with no initializer holds: §6.8's Table 6-7
// gives a 4-state integral variable x, which CreateVariable filled, and a
// 2-state one 0. A string and a real are registered as such, since a read of
// either goes through the kind rather than through the bits. §15.5 (printed
// page 378): a variable declared `event` is a named event, which `-> e`
// triggers, `@e` waits on and `e.triggered` reads, each through
// Variable::is_event as a module's is marked by LowerVar (lowerer_var.cpp);
// left clear, a package's `event e` was a one-bit value `-> p1::e` marked
// but nothing waited on or read as an event. §8.4 (printed 181-182), Table
// 8-1: a handle's default is null, the 0 a class handle carries
// (kNullClassHandle) and a semaphore's or mailbox's carrier holds for no
// object (sync_variable.h), so a handle is two-state whatever its named
// type's spelling says; taken as a 4-state named type, a package's `mailbox
// bare` or `C h` with no initializer was filled with x, `p::bare == null`
// read x and every sum it stood in x.
static void ShapePackageVariable(const ModuleItem* item, Variable* var,
                                 std::string_view qname, SimContext& ctx,
                                 Arena& arena) {
  const DataType& type = item->data_type;
  var->is_4state =
      DeclaredTypeIs4State(type) && !PackageItemIsHandle(item, qname, ctx);
  var->is_signed = DeclaredTypeIsSigned(type, ctx);
  var->value.is_signed = var->is_signed;
  var->is_event = type.kind == DataTypeKind::kEvent;
  if (!var->is_4state)
    var->value = MakeLogic4VecVal(arena, var->value.width, 0);
  if (DeclaredTypeIsString(type, ctx)) ctx.RegisterStringVariable(qname);
  bool is_real = type.kind == DataTypeKind::kReal ||
                 type.kind == DataTypeKind::kShortreal ||
                 type.kind == DataTypeKind::kRealtime;
  var->is_real = is_real;
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

// §3.12.1 (printed page 56): the name the compilation-unit scope's items
// are keyed and their frames named by, in the place of a package's name --
// one no package can be declared with, `$` starting no identifier, as
// SubroutineImportScopeKey (lowerer_import.cpp) spells a module
// subroutine's own imports.
constexpr std::string_view kUnitScope = "$unit";

// The key a data item's storage stands under: "pk.name" for a package's,
// the one EvalMemberAccess reads a `pk::name` by, and "$unit.name" for the
// compilation unit's (§3.12.1), for which `pkg` is kUnitScope -- a key no
// module's declaration is keyed by, so a top-level module's own `int g`,
// stored under the bare name, leaves the unit's g standing; stored under
// the bare name itself, the unit's was replaced by the top's LowerVar and
// taken for the top's port by CreatePortVariable (lowerer_register.cpp),
// which creates a port's storage only where nothing answers the name.
static std::string PackageDataKey(const ModuleItem* item,
                                  std::string_view pkg) {
  return std::string(pkg) + "." + std::string(item->name);
}

// §6.20.2 (printed pages 126-127): whether a parameter's declaration fixes
// its width -- by a range or a type other than the implicit one, as
// HasDeclaredWidth (src/elaborator/const_eval_bits.cpp) reads it off a
// module's RtlirParamDecl -- and not by a real, shortreal or realtime type,
// whose value is a real that no vector width sizes (§6.12). One declared with
// neither takes the width of its value.
static bool ParamDeclaresAWidth(const ModuleItem* item) {
  const DataType& type = item->data_type;
  if (type.packed_dim_left == nullptr && type.kind == DataTypeKind::kImplicit)
    return false;
  return type.kind != DataTypeKind::kReal &&
         type.kind != DataTypeKind::kShortreal &&
         type.kind != DataTypeKind::kRealtime;
}

// The width a parameter's declaration fixes as far as it folds with no name
// in scope, for the storage created before any parameter holds a value; 0
// where the declaration fixes none or a range's bound names a parameter, the
// storage then taking 32 bits until the initializer's own width replaces it
// (InitPackageParam).
static uint32_t DeclaredParamStorageWidth(const ModuleItem* item,
                                          SimContext& ctx) {
  if (!ParamDeclaresAWidth(item)) return 0;
  const DataType& type = item->data_type;
  if (type.packed_dim_left != nullptr) return PackedDimProduct(type);
  return DeclaredTypeWidth(type, ctx);
}

// The width a parameter's declaration fixes, its range evaluated in the
// package's frame where §6.20.1 lets a bound name an earlier parameter --
// `logic [N-1:0] M` after `int N = 12` is twelve bits -- and 0 where the
// declaration fixes none. Folded with no parameter in scope, `[N-1:0]` fell
// to the base type's one bit and M held a single bit.
static uint32_t DeclaredParamWidth(const ModuleItem* item, SimContext& ctx,
                                   Arena& arena) {
  if (!ParamDeclaresAWidth(item)) return 0;
  const DataType& type = item->data_type;
  if (type.packed_dim_left != nullptr)
    return EvalFormalArgWidth(type, ctx, arena);
  return DeclaredTypeWidth(type, ctx);
}

// The width of a data item's storage: a variable's declared type's, a
// parameter's the range or the type its declaration fixes, and a parameter
// declared with neither, or a type no table sizes, 32 bits. §8.3 (printed page
// 180) with §8.4: a variable of a class type holds a handle to an object, which
// Lowerer::LowerVar sizes at 64 bits whatever the declaration's own width
// says (StorageWidth in lowerer_var.cpp); a package's is known to be one by
// the class record RegisterPackageClassVariables entered under `qname` ahead
// of this -- the package's own class, an imported one, or the built-in
// process or weak_reference class -- so its carrier is sized the same. Sized
// at 32, a handle written through `p1::h = new` was held in half its bits.
// §7.10 (printed 169), §7.5 and §7.4.2 (printed 154): a queue, a dynamic
// array or a fixed-size array declared with the class's name, `C q[$]`,
// `C d[]` or `C arr[2]`, is an array whose every element is such a handle,
// and the width answered here is the element's -- the queue's elem_width,
// the dynamic array's ArrayInfo and each element variable of the fixed-size
// array -- so it is a handle's 64 bits too. The class record is entered for
// the declaration whatever its dimensions, and a scalar alone was sized by
// it, so an element of any of the three held an object id in 32 bits and an
// id above 2^32 was truncated. §15.3 (printed 372) and §15.4 (printed 374):
// a package's `semaphore s` or `mailbox mb` is a handle too, of no class
// record, so it is sized by its type's spelling (PackageItemIsHandle);
// sized at 32, the object's identity (SyncObjectIdentity) was held in half
// its bits.
static uint32_t PackageDataWidth(const ModuleItem* item, std::string_view qname,
                                 SimContext& ctx) {
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  uint32_t width = is_var ? DeclaredTypeWidth(item->data_type, ctx)
                          : DeclaredParamStorageWidth(item, ctx);
  if (width != 0) return width;
  return PackageItemIsHandle(item, qname, ctx) ? 64 : 32;
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

// §7.4.2 (printed page 154): the package array `item` declares, shaped as
// the RtlirVariable CreateArrayElements (lowerer_var.cpp) reads a module's
// from -- its element type as ShapePackageVariable shapes the carrier, its
// unpacked extents folded in the package's frame -- with the declaration's
// initializer `init`, which CreateArrayElements distributes one item per
// element (§10.9.1), or none. None where a dimension does not fold.
static std::optional<RtlirVariable> PackageArrayShape(const ModuleItem* item,
                                                      std::string_view pkg,
                                                      const Expr* init,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  const DataType& type = item->data_type;
  RtlirVariable var;
  var.name = item->name;
  var.width = PackageDataWidth(item, PackageDataKey(item, pkg), ctx);
  var.is_4state = DeclaredTypeIs4State(type);
  var.is_signed = DeclaredTypeIsSigned(type, ctx);
  var.is_string = DeclaredTypeIsString(type, ctx);
  var.is_real = type.kind == DataTypeKind::kReal ||
                type.kind == DataTypeKind::kShortreal ||
                type.kind == DataTypeKind::kRealtime;
  var.init_expr = init;
  var.dtype = &type;
  var.elem_type_kind = type.kind;
  if (!FoldPackageArrayDims(item, pkg, var, ctx, arena)) return std::nullopt;
  return var;
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
// as one bit, and foreach ran once per bit of the carrier. The elements are
// made at §6.8's Table 6-7 defaults here, the declaration's initializer left
// for InitPackageArray: §26.6 (printed pages 815-816) lets an item of the
// pattern name what another package's export hands on, `'{VAL2, x}` after
// `import p2::*`, which is bound between this and InitPackageDataVariables
// (AliasPackageExports, lowerer_import.cpp); distributed here, such an item
// found no "p2.VAL2" and read 0.
static void CreatePackageArray(const ModuleItem* item, std::string_view pkg,
                               std::string_view qname, SimContext& ctx,
                               Arena& arena) {
  std::optional<RtlirVariable> var =
      PackageArrayShape(item, pkg, nullptr, ctx, arena);
  if (!var) return;
  ctx.PushScope(pkg);
  CreateArrayElements(qname, *var, ctx, arena);
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

// §15.3 (printed page 372) and §15.4 (printed 374) with §26.2 (printed
// 808): a package's `semaphore s` is the bucket of keys its get(), put() and
// try_get() operate on, and its `mailbox mb` the queue its put(), get(),
// peek(), num() and try_ methods pass messages through, each made under the
// "pk.name" key its carrier variable stands under, as CreateSyncObjectForVar
// (sync_variable.cpp) makes a module's, so that
// SemaphoreCallTarget (eval_semaphore.cpp) and MailboxCallTarget
// (eval_mailbox.cpp) find it by the key a `p1::s` receiver resolves to, the
// key the package's own task or function reaches a bare `s` by through
// ScopedObjectKeys, and the key an import aliases (AliasSemaphore in
// lowerer_import.cpp). The bucket starts empty and the queue unbounded, as a
// module's do with no initializer; a declaration assignment sizes either in
// InitPackageSyncObject once the package's earlier items hold their values.
// The carrier alone stood there for a mailbox, the new() evaluated into it
// and no MailboxObject made under "p1.mb", so `p1::mb.put(7)` placed
// nothing, `p1::mb.get(a)` retrieved nothing and left a unwritten, and num()
// and try_put() were served by no mailbox -- 61223c5d5's remainder, which
// created a module's alone.
static void CreatePackageSyncObject(std::string_view type,
                                    std::string_view qname, SimContext& ctx) {
  if (type == "semaphore") ctx.CreateSemaphore(qname, 0);
  if (type == "mailbox") ctx.CreateMailbox(qname, 0);
}

// §15.3.1 (printed page 373) and §15.4.1 (printed 374) with §26.2 (printed
// 808): a semaphore's declaration assignment is a new() whose one argument
// is the number of keys the bucket starts with, none when it is absent, and
// a mailbox's a new() whose one argument is the bound, 0 and unbounded when
// it is absent; the argument is an expression of the package's scope, read
// in the package's frame as InitScopeDataItems reads every other
// initializer, after the package's parameters and earlier variables hold
// their values, so `new(D)` reads the package's own D (§11.2.1). Read when
// the object was created, ahead of the parameters' own initializers, D was
// the 0 its storage was created with, and the bucket started empty and the
// queue unbounded whatever the declaration wrote. The new() returns the
// handle the variable holds, so the variable under the key is marked held
// (HoldSyncVariable in sync_variable.cpp), as a module's declaration
// marks its own; left at the 0 its storage was created with, §8.4 (printed
// 181-182) compared `p::mb` equal to null after its `= new`. True for a
// semaphore's or a mailbox's item whatever its initializer.
static bool InitPackageSyncObject(const ModuleItem* item, std::string_view key,
                                  SimContext& ctx, Arena& arena) {
  std::string_view type = PackageSyncObjectType(item);
  if (type.empty()) return false;
  const Expr* init = item->init_expr;
  if (init->kind != ExprKind::kCall || init->text != "new") return true;
  if (type == "semaphore") {
    if (SemaphoreObject* sem = ctx.FindSemaphore(key))
      sem->key_count = SemaphoreKeyArg(init, ctx, arena, 0);
  } else if (MailboxObject* mbx = ctx.FindMailbox(key)) {
    mbx->Build(MailboxBoundArg(init, ctx, arena));
  }
  HoldSyncVariable(key, ctx);
  return true;
}

// §8.3 (printed page 180) with §8.25 (printed 203): the class a unit
// variable is declared with and the specialization it wrote, which
// RegisterUnitClassVariables (lowerer_register.cpp) recorded under the
// item's bare name, the name a module's `h = new` asks the class of
// (TryClassNewAssign), carried to the "$unit.name" key its storage stands
// under, which PackageDataWidth sizes the storage by and
// ConstructClassNewInit constructs and binds by. Nothing for an item of no
// class type.
static void CarryUnitClassRecord(const ModuleItem* item, std::string_view qname,
                                 SimContext& ctx) {
  std::string_view cls = ctx.GetVariableClassType(item->name);
  if (cls.empty()) return;
  ctx.SetVariableClassType(qname, cls);
  RecordClassParamActuals(qname, item->data_type.type_params, ctx);
}

// §7.2.1 (printed page 147) with §3.12.1 (printed 56) and §26.2 (printed
// 808): a package's or the unit's variable of a packed structure or union
// type is laid out as its type lays its members out, so a member read or
// write of it, `$unit::u.b` or `p::u.b`, is the window of bits the layout
// gives the member (ResolveMemberByType in eval_expr.cpp, through
// StructLayoutOfName), a by-value formal bound from `f($unit::u)` takes the
// variable's layout (TryBindIdentifierActualLayout in
// eval_function_args.cpp) and a tagged union's tag stands under the key the
// layout answers for (TagKeyOfName). The layout is registered under the
// storage's "pk.name" or "$unit.name" key as Lowerer::LowerVar registers a
// module's under the variable's name: built from the declaration for a
// structure written inline, and for a typedef name bound to the typedef's
// own layout, which RegisterDesignTypeLayouts (lowerer_var_layout.cpp)
// registers under the name the design's typedef table keys it by -- the
// bare name for the unit's typedef, "pk::name" for the package's own, and
// "scope::name" for one written with a scope. No layout stood under the
// key, so `$unit::u.b` read through no member and answered 0, and a formal
// bound from `f($unit::u)` fell back to its typedef's layout.
static void RegisterPackageDataLayout(const ModuleItem* item,
                                      std::string_view pkg,
                                      std::string_view qname, SimContext& ctx,
                                      Arena& arena) {
  const DataType& type = item->data_type;
  if (!type.struct_members.empty()) {
    RegisterAggregateLayout(qname, &type, PackageDataWidth(item, qname, ctx),
                            ctx, arena);
    return;
  }
  if (type.kind != DataTypeKind::kNamed) return;
  std::string scoped =
      std::string(type.scope_name.empty() ? pkg : type.scope_name) +
      "::" + std::string(type.type_name);
  const StructTypeInfo* info = ctx.FindStructType(scoped);
  if (info == nullptr) info = ctx.FindStructType(type.type_name);
  if (info != nullptr) ctx.SetVariableStructType(qname, info->type_name);
}

// One data item's storage under its key: every variable declaration at its
// declared type's shape, with the semaphore, the mailbox, the queue or the
// array its type or dimension declares, and a parameter with an initializer
// as a constant of its declared width, or of 32 bits where the declaration
// fixes none. The initializer is evaluated by InitPackageDataItem
// once every scope's storage exists. Answers the interned key, empty for an
// item declaring no data.
// §6.19.5 with §26.3: a package's variable or parameter declared with an
// enumeration's typedef, `color_t pc` or `parameter color_t EC`, is an
// expression of that type wherever it is named -- `P::pc.next()`, `EC.name()`
// through an import -- so the enumeration is recorded under the storage's
// key, by the typedef's "pk::name" key when the package's own typedef or a
// scoped one is written and by the bare name otherwise. Unrecorded, the
// methods found no enumeration under the key and answered 0 or "".
static void RegisterPackageDataEnumType(const ModuleItem* item,
                                        std::string_view pkg,
                                        std::string_view qname,
                                        SimContext& ctx) {
  const DataType& type = item->data_type;
  if (type.kind != DataTypeKind::kNamed) return;
  std::string scoped =
      std::string(type.scope_name.empty() ? pkg : type.scope_name) +
      "::" + std::string(type.type_name);
  const EnumTypeInfo* info = ctx.FindEnumType(scoped);
  if (info == nullptr) info = ctx.FindEnumType(type.type_name);
  if (info != nullptr) ctx.SetVariableEnumType(qname, info->type_name);
}

static std::string_view CreatePackageDataItem(const ModuleItem* item,
                                              std::string_view pkg,
                                              SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item)) return {};
  auto* qname = arena.Create<std::string>(PackageDataKey(item, pkg));
  if (pkg == kUnitScope) CarryUnitClassRecord(item, *qname, ctx);
  auto* var = ctx.CreateVariable(*qname, PackageDataWidth(item, *qname, ctx));
  RegisterPackageDataEnumType(item, pkg, *qname, ctx);
  if (item->kind != ModuleItemKind::kVarDecl) return *qname;
  ShapePackageVariable(item, var, *qname, ctx, arena);
  RegisterPackageDataLayout(item, pkg, *qname, ctx, arena);
  std::string_view sync_type = PackageSyncObjectType(item);
  if (!sync_type.empty()) {
    CreatePackageSyncObject(sync_type, *qname, ctx);
    return *qname;
  }
  CreatePackageAggregate(item, pkg, *qname, ctx, arena);
  return *qname;
}

void CreatePackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items)
      CreatePackageDataItem(item, pkg->name, ctx, arena);
  }
}

// §3.12.1 (printed page 56) with §6.21 (printed 132-133): the compilation-unit
// scope holds the declarations outside any other scope, and a name referenced
// in a module that the module's own scope does not declare is searched for in
// the compilation-unit scope next, so `int g;` written outside every module
// is one variable every module of the unit reads and writes. Its storage
// stands under "$unit.g" (PackageDataKey), the key the unit's own frame
// resolves a bare name to (InitScopeDataItems) and each module's bare
// reference is bound to under the module's prefix (AliasUnitDataItems), the
// bare key for a top-level module and "u.g" for an instance. No path
// created the storage before, so a module's write to `g` landed nowhere and
// a read answered nothing. §26.2 keeps a package from naming the unit's
// items, so the packages' storage above is created first and the unit's
// after. §8.3 (printed 180): a unit variable of a class type, `C h;` after
// a unit `class C`, holds a handle, which PackageDataWidth sizes at a
// handle's 64 bits by the class record RegisterUnitClassVariables
// (lowerer_register.cpp) entered under the bare name ahead of this and
// CarryUnitClassRecord carries to the storage's key; with no record, the
// packages' alone being entered, the storage was 32 bits and `h = new`
// constructed nothing.
void CreateUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena) {
  if (design->compilation_unit == nullptr) return;
  for (auto* item : design->compilation_unit->cu_items)
    CreatePackageDataItem(item, kUnitScope, ctx, arena);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761) and §6.21 (printed
// 132-133): a reference the module's own scope does not declare is resolved
// in the compilation-unit scope next, so each of the unit's data items the
// module `mod` does not declare -- as a variable, a port or a net
// (ModuleDeclaresName) -- is bound under the module's `inst_prefix` to the
// unit's storage, "g" for a top and "u.g" for an instance, with the queue,
// the array, the class record and the other kinds the storage carries
// (AliasVariableKinds), as an import's name is bound
// (Lowerer::AliasImportedPackageName), and registered as a name bound
// outside every module so that SimContext::FindVariable crosses §23.9's
// boundary to the top's bare key from a generate block's process. A key the
// module's imports or its parameters already hold is left to them (§26.5,
// the import being the nearer scope's), and a name the module declares to
// the declaration, which the nearer scope's lookup finds first. With the
// unit's storage under the bare name alone, the top's `int g = 7` replaced
// it and every instance's bare `g`, answered from that key, read the top's 7
// for the unit's 5, and the top's `input int g` was the unit's variable.
void AliasUnitDataItems(const RtlirDesign* design, const RtlirModule* mod,
                        std::string_view inst_prefix, SimContext& ctx,
                        Arena& arena) {
  if (design->compilation_unit == nullptr) return;
  for (const auto* item : design->compilation_unit->cu_items) {
    if (!DeclaresPackageData(item) || ModuleDeclaresName(mod, item->name))
      continue;
    std::string key = std::string(inst_prefix) + std::string(item->name);
    if (ctx.GetVariables().count(key) != 0) continue;
    std::string_view stored = *arena.Create<std::string>(key);
    std::string qname = PackageDataKey(item, kUnitScope);
    ctx.AliasVariable(stored, qname);
    AliasVariableKinds(stored, qname, ctx, arena);
    ctx.RegisterImportedName(stored);
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

// §7.4.2 (printed page 154) with §10.9.1 and §26.2 (printed 808): a package
// fixed-size array's declaration assignment, `int a[2] = '{VAL2, x}`, gives
// each element the pattern item that reaches it, distributed by
// InitArrayElements (lowerer_var.cpp) as CreateArrayElements distributes a
// module's, one item per element, keyed, replicated or positional, in the
// package's frame the caller has pushed, and written into the element
// variables CreatePackageArray made at their defaults. §26.6 (printed pages
// 815-816): an export binds the exporting package's keys to those very
// element variables (AliasArray in lowerer_import.cpp) between their
// creation and this, so the items land where `q::a[1]` through the
// exporter reads and `q::a[0] = 9` writes; remade under the same keys
// holding the items' values, as they were, the elements the export had
// bound went stale, `q::a[1]` after p's `int a[2] = '{1, 2}` read 0 and a
// write through the exporter never reached p's own element. True where
// `key` holds a fixed-size array, whose carrier the initializer must not
// reach. Made here rather than at creation, an item naming what another
// package's export hands on reads the exported declaration; at creation it
// read 0.
static bool InitPackageArray(const ModuleItem* item, std::string_view pkg,
                             std::string_view key, SimContext& ctx,
                             Arena& arena) {
  if (ctx.FindArrayInfo(key) == nullptr || ctx.FindQueue(key) != nullptr)
    return false;
  std::optional<RtlirVariable> var =
      PackageArrayShape(item, pkg, item->init_expr, ctx, arena);
  if (var) InitArrayElements(key, *var, ctx, arena);
  return true;
}

// §8.7 (printed page 184) with §8.3 (printed 180): whether the data item
// `key` is a variable of a class type -- one the class record entered under
// its key ahead of the storage names (RegisterPackageClassVariables) --
// whose declaration assignment is a `new` call, `C h = new;` or `G #(5) b =
// new(3);`, which constructs an object of the class rather than naming a
// value the carrier could hold.
static bool IsClassNewInit(const ModuleItem* item, std::string_view key,
                           SimContext& ctx) {
  const Expr* init = item->init_expr;
  if (init == nullptr || init->kind != ExprKind::kCall || init->text != "new")
    return false;
  return !ctx.GetVariableClassType(key).empty();
}

// §10.9.2 (printed page 263) with §7.2.1 (printed 147): a structure
// variable's assignment-pattern initializer, keyed or positional, is
// evaluated against the layout RegisterPackageDataLayout registered under
// `key`, each member expression coerced to its member, as
// Lowerer::LowerVarInit (lowerer_var.cpp) evaluates a module's; with no
// layout the pattern is concatenated at its items' self-determined widths,
// so `'{b: 12'hBCD, a: 4'hA}` placed b's item where a's bits are. §11.9
// (printed 304) with §7.3.2 (printed 151): a tagged union variable's
// `tagged Valid 9` initializer sets the variable's tag beside its bits,
// recorded under the storage's key, the one every reader of the tag
// resolves the name to (TagKeyOfName), interned as 9183540f7 interns a
// procedural assignment's since SimContext::var_tags_ keeps the view it is
// given. No tag was recorded, so `$unit::u.Other` and `a.Other` through a
// formal bound from `f($unit::u)` were checked against nothing and read
// the 9 unreported. Every other initializer is the carrier's value as it
// was.
static void InitPackageCarrier(const Expr* init, std::string_view key,
                               Variable* var, SimContext& ctx, Arena& arena) {
  const StructTypeInfo* sinfo = ctx.GetVariableStructType(key);
  const Expr* pattern = UnwrapTypedPattern(init);
  if (sinfo != nullptr && pattern->kind == ExprKind::kAssignmentPattern) {
    var->value = EvalStructPatternValue(pattern, sinfo, ctx, arena);
    return;
  }
  var->value = EvalExpr(init, ctx, arena);
  if (init->kind != ExprKind::kTagged || init->rhs == nullptr) return;
  ctx.SetVariableTag(*arena.Create<std::string>(std::string(key)),
                     init->rhs->text);
}

// §6.20.2 (printed pages 126-127) with §11.6.1 (printed 299): a parameter
// declared with a range or a type keeps that range whatever its value, and
// its initializer is the right-hand side of an assignment to it, so the
// value is evaluated at the declared width -- an unbased unsized literal
// filling it (§5.7.1), a narrower operand extended to it -- and cut or
// extended to that width, as Lowerer::LowerParams with ReevaluateParamValue
// (lowerer_register.cpp) size a module's. A parameter declared with neither
// takes the range of its value, which is its self-determined evaluation. The
// words are copied because an initializer that is a bare name answers that
// name's own storage. Evaluated self-determined and stored whole whatever
// the declaration said, `parameter logic [11:0] W = '1` held the literal's
// 64-bit carrier and `p::W` read 18446744073709551615 for 4095.
static void InitPackageParam(const ModuleItem* item, Variable* var,
                             SimContext& ctx, Arena& arena) {
  uint32_t width = DeclaredParamWidth(item, ctx, arena);
  if (width == 0) {
    var->value = EvalExpr(item->init_expr, ctx, arena);
    return;
  }
  Logic4Vec value = EvalExpr(item->init_expr, ctx, arena, width);
  var->value = OwnRhsWords(ResizeToWidth(value, width, arena), arena);
}

// One data item's initializer, evaluated into the storage
// CreatePackageDataItem gave it; an item declaring no data, or none, has
// nothing to evaluate. §15.3.1 and §15.4.1: a semaphore's or a mailbox's
// initializer is the new() that sizes the object (InitPackageSyncObject) and
// names no value the carrier variable holds, so the carrier is left alone, as
// it is for a class variable's `new` (IsClassNewInit), which names a
// construction ConstructDataClassInitializers makes once the class exists. A
// fixed-size array's is distributed over the elements (InitPackageArray,
// §7.4.2), and a queue's, a dynamic array's or an associative array's fills
// the object (InitPackageAggregate); a parameter's is sized by its
// declaration (InitPackageParam), and every other initializer is the carrier
// variable's value, a structure's placed by its layout and a tagged union's
// recording its tag (InitPackageCarrier).
static void InitPackageDataItem(const ModuleItem* item, std::string_view pkg,
                                SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item) || item->init_expr == nullptr) return;
  std::string key = PackageDataKey(item, pkg);
  if (InitPackageSyncObject(item, key, ctx, arena)) return;
  if (IsClassNewInit(item, key, ctx)) return;
  if (InitPackageArray(item, pkg, key, ctx, arena)) return;
  if (InitPackageAggregate(item->init_expr, key, ctx, arena)) return;
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  if (found == variables.end()) return;
  if (item->kind == ModuleItemKind::kParamDecl) {
    InitPackageParam(item, found->second, ctx, arena);
    return;
  }
  InitPackageCarrier(item->init_expr, key, found->second, ctx, arena);
}

// §26.2 with §26.3: the initializers of one scope's items, evaluated in the
// scope's frame: for a package, the frame a package subroutine's body runs
// in, which resolves the package's earlier variables, its subroutines and
// those an import brings in by their bare names
// (SimContext::FindInPackageScope and FindFunctionInPackageScope); for the
// compilation unit, a frame named kUnitScope, through which a bare name
// reaches the unit's own storage under its "$unit.name" key ahead of any
// module's, and a name the unit's imports bound under the bare key
// (Lowerer::LowerCompilationUnitImports) as a frame of no package would.
static void InitScopeDataItems(const std::vector<ModuleItem*>& items,
                               std::string_view pkg, SimContext& ctx,
                               Arena& arena) {
  ctx.PushScope(pkg);
  for (auto* item : items) InitPackageDataItem(item, pkg, ctx, arena);
  ctx.PopScope();
}

void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  // §26.6 (printed pages 815-816): a name an import brings in through
  // another package's export is the original declaration, bound under the
  // exporter's key by AliasPackageExports (lowerer_import.cpp), which runs
  // between CreatePackageDataVariables and this so that p3's `int q = x`
  // after `import p2::*` reads p1's x through p2's `export p1::*`; evaluated
  // ahead of the exports, it read 0.
  for (auto* pkg : design->packages)
    InitScopeDataItems(pkg->items, pkg->name, ctx, arena);
}

void InitUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                           Arena& arena) {
  // §3.12.1 with §26.2 (printed page 808): a unit item's declaration
  // assignment is made before any initial or always procedure starts, as a
  // package's is, and it may read the packages' items an import of the unit
  // makes visible (§26.3, printed 810), so it follows the packages'
  // initializers and the unit's imports, which Lowerer::InitCompilationUnitData
  // (lowerer_data_init.cpp) binds just ahead of this; bound after this, the
  // imports left `import p::*; int g = K;` reading no K, and g 0.
  if (design->compilation_unit == nullptr) return;
  InitScopeDataItems(design->compilation_unit->cu_items, kUnitScope, ctx,
                     arena);
}

// §8.7 (printed page 184) with §6.8 and §26.2 (printed 808): `C h = new;`
// among a package's items constructs an object of C as the package's
// declaration assignment, as TryLowerClassNewVarInit (lowerer_var.cpp)
// constructs a module's, and §8.25 (printed 203) has the object be of the
// specialization the declaration wrote, `G #(5) b = new`, whose actuals
// RegisterPackageClassVariables recorded under the item's key for
// ApplyClassParamOverrides to bind on the object, as the module path binds
// them. A bare `new` names no class of its own, so InitPackageDataItem,
// which evaluated it as an ordinary expression, constructed nothing and
// bound nothing, and `p1::b.get_n()` ran on no object, reading N's default
// 1 where the specialization gives 5. The construction is made in the
// scope's frame, as InitScopeDataItems evaluates the other initializers, so
// a constructor argument reads the scope's own names. §8.30.1 (printed
// 217): the built-in weak_reference class, which the run holds no record of
// under the class type's key, has its own `new(obj)`, taken through
// EvalWeakReferenceNew (statement_assign_object.cpp), the one mechanism the
// procedural `w = new(h)` takes, so `weak_reference #(C) w = new(h);` among
// a package's or the unit's items refers to the object the scope's earlier
// `C h = new;` constructed; skipped as a class with no record, the
// declaration form was constructed by nothing and `p::w.get()` answered
// null. Nothing is made for any other class the run holds no record of,
// and §8.12's `= new src` copy is not taken, as the module path takes none.
static void ConstructClassNewInit(const ModuleItem* item, std::string_view pkg,
                                  SimContext& ctx, Arena& arena) {
  if (item->kind != ModuleItemKind::kVarDecl) return;
  std::string key = PackageDataKey(item, pkg);
  if (!IsClassNewInit(item, key, ctx)) return;
  std::string_view cls = ctx.GetVariableClassType(key);
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  if (found == variables.end()) return;
  const Expr* init = item->init_expr;
  if (cls == "weak_reference") {
    found->second->value = EvalWeakReferenceNew(init, ctx, arena);
    return;
  }
  if (ctx.FindClassType(cls) == nullptr) return;
  found->second->value = EvalClassNew(cls, init, ctx, arena, init->range.start);
  ApplyClassParamOverrides(key, found->second->value.ToUint64(), ctx, arena);
}

// The constructions of one scope's items, in the scope's frame.
static void ConstructScopeClassInits(const std::vector<ModuleItem*>& items,
                                     std::string_view pkg, SimContext& ctx,
                                     Arena& arena) {
  ctx.PushScope(pkg);
  for (auto* item : items) ConstructClassNewInit(item, pkg, ctx, arena);
  ctx.PopScope();
}

void ConstructDataClassInitializers(const RtlirDesign* design, SimContext& ctx,
                                    Arena& arena) {
  // §26.2 with §3.12.1: a package's classes are lowered after the packages'
  // and the unit's other initializers (Lowerer::LowerUnimportedPackageClasses,
  // the imports having lowered some earlier) and the unit's after the unit's
  // initializers (LowerCompilationUnitClasses), so the constructions wait
  // for both rather than running with the other initializers, ahead of
  // which no class of either scope was lowered and EvalClassNew found none;
  // the packages' first, the unit's after, in the order the initializers
  // were made. §6.21 (printed pages 132-133): a module's variable is
  // initialized at its declaration, ahead of the module's procedures, so the
  // constructions run before any module is lowered
  // (Lowerer::ConstructDesignData in lowerer_data_init.cpp); run after the
  // modules, they came after a module's `int y = p1::b.get_n();`, which
  // called the method on a null handle.
  for (auto* pkg : design->packages)
    ConstructScopeClassInits(pkg->items, pkg->name, ctx, arena);
  if (design->compilation_unit == nullptr) return;
  ConstructScopeClassInits(design->compilation_unit->cu_items, kUnitScope, ctx,
                           arena);
}

}  // namespace delta
