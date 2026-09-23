// The blocking assignments whose left-hand side names an object rather than a
// vector: §7.9's associative-array whole-array forms and §8.3's class `new`.
//
// §7.9.11 lets a whole associative array be written at once -- by copying
// another array, by assigning the result of §7.12.5's map(), or from an
// '{index:value} literal -- and §8.3 has `new` construct a class object and
// return the handle the target then holds, in the bare, the shallow-copy, the
// class-scope `C::new`, the `obj.field = new` and the `C::field = new` forms.
// Neither family sizes a right-hand value against the width of its target the
// way §10.7 does for a vector, so each is answered whole before the generic
// path evaluates an rhs at all, and all of them are reached from one run of
// TryDispatchSpecialBlockingAssign.
//
// That dispatch, and the vector-target writers around it, stay in
// src/simulator/statement_assign_core.cpp, which reached 948 lines against the
// 950 assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails
// at. The names this side owes that one are declared in
// simulator/statement_assign_internal.h, save TryClassNewAssign, which
// simulator/statement_assign.h already declares for eval_function_body.cpp.

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §7.9.9 (printed page 168): assigning one associative array to another
// clears the target and copies each entry of the source into it. Either side
// may be a class property (§8.5) -- by its bare name in a method, through a
// handle, `b.m = a.m`, or `C::m` -- which FindAssocArrayOfBase resolves as a
// declared array's name is; asked by name alone, a property on either side
// found no array and the assignment did nothing, which lost every edge set
// UVM's uvm_phase::add copies with `end_node.m_successors =
// after_phase.m_successors;`.
bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto* dst = FindAssocArrayOfBase(stmt->lhs, ctx, arena);
  if (!dst) return false;
  auto* src = FindAssocArrayOfBase(stmt->rhs, ctx, arena);
  if (!src) return false;
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

// §7.12.5 — assigning the result of `src.map() with (...)` to an
// associative-array target, where the source is itself an associative array.
// map() returns an array whose set of index values matches the source, with
// each stored value replaced by the value of the with expression; copy those
// key/value pairs into the destination, replacing its previous contents. This
// is the associative analogue of the indexed-array map (whose result flows
// through the queue/dynamic-array element-collection path); without it a bare
// `dst = src.map() with (...)` between two associative arrays would leave the
// destination empty.
bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  if (!dst) return false;
  AssocArrayObject mapped;
  if (!TryCollectAssocMapResult(stmt->rhs, ctx, arena, mapped)) return false;
  dst->int_data = mapped.int_data;
  dst->str_data = mapped.str_data;
  return true;
}

static std::string StripAssocKeyQuotes(std::string_view key) {
  if (key.size() >= 2 && key.front() == '"' && key.back() == '"')
    return std::string(key.substr(1, key.size() - 2));
  return std::string(key);
}

// §7.9.11: besides writing an associative array one entry at a time, the whole
// array contents can be replaced by assigning an '{index:value} array literal.
// Discard the existing entries and repopulate keyed entries and the optional
// default from the pattern, mirroring the declaration-time initialization.
bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kAssignmentPattern)
    return false;
  if (stmt->rhs->pattern_keys.empty()) return false;
  auto* aa = ctx.FindAssocArray(stmt->lhs->text);
  if (!aa) return false;
  aa->int_data.clear();
  aa->str_data.clear();
  const Expr* rhs = stmt->rhs;
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    const auto* key = rhs->pattern_keys[i];
    auto val = EvalExpr(rhs->elements[i], ctx, arena);
    if (key->text == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripAssocKeyQuotes(key->text)] = val;
    } else {
      // §7.9.11: the entry goes at the index the key evaluates to, read as an
      // index of this array's declared index type -- the same reading a key
      // written on the left of a single-element assignment gets.
      auto key_val = EvalExpr(key, ctx, arena);
      aa->int_data[AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                               aa->is_index_signed)] = val;
    }
  }
  return true;
}

// `new src_obj` shallow-copy form: returns true (and writes the copy handle to
// the target) when the rhs argument resolves to an existing class object.
static bool TryClassCopyNewAssign(const Stmt* stmt, std::string_view target,
                                  SimContext& ctx, Arena& arena) {
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto src_val = EvalExpr(stmt->rhs->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, copy_handle);
    var->NotifyWatchers();
  }
  return true;
}

// §8.30.1 (printed page 217 of IEEE 1800-2023): the `new(referent)` of
// the built-in weak_reference class, which names no class the run holds a
// record of, allocates the weak reference to the object the one argument refers
// to
// -- a null reference with no argument -- and answers its handle as the
// 64-bit value the variable of the weak_reference type holds. One mechanism
// for the procedural `w = new(h)` below and for a package's or the unit's
// `weak_reference #(C) w = new(h);` declaration assignment
// (ConstructClassNewInit in lowerer_package_data.cpp); with the allocation
// static here, the declaration form was constructed by nothing and
// `p::w.get()` answered null.
Logic4Vec EvalWeakReferenceNew(const Expr* call, SimContext& ctx,
                               Arena& arena) {
  uint64_t referent = kNullClassHandle;
  if (!call->args.empty())
    referent = EvalExpr(call->args[0], ctx, arena).ToUint64();
  return MakeLogic4VecVal(arena, 64,
                          ctx.AllocateWeakReference(referent, arena));
}

// `new (referent)` for a weak_reference-typed target: allocate the weak
// reference wrapper and write its handle to the target.
static void AssignWeakReferenceNew(const Stmt* stmt, std::string_view target,
                                   SimContext& ctx, Arena& arena) {
  Logic4Vec wr_handle = EvalWeakReferenceNew(stmt->rhs, ctx, arena);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = wr_handle;
    var->NotifyWatchers();
  }
}

// The key the storage of a `new`'s target is held under, and its class
// recorded under: a variable's own name, and for a package variable named
// through the package scope resolution operator (§26.3), `p::h = new`, the
// "p.h" InitPackageDataVariables creates the storage under and
// RegisterPackageClassVariables records the class under. `C::x = new` on a
// class's static property has the same shape and is answered by no class
// record under "C.x", which leaves it to TryMemberClassNewAssign. Empty for
// any other target.
static std::string_view ClassNewTargetKey(const Expr* lhs, Arena& arena) {
  if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      !lhs->lhs || lhs->lhs->kind != ExprKind::kIdentifier || !lhs->rhs ||
      lhs->rhs->kind != ExprKind::kIdentifier)
    return {};
  return *arena.Create<std::string>(std::string(lhs->lhs->text) + "." +
                                    std::string(lhs->rhs->text));
}

// §7.5.1 (printed page 158) with §8.4 (printed 181): the class a declaration
// records under an array's name (SetVariableClassType by Lowerer::LowerVar,
// ExecVarDeclImpl and CreateFuncLocalVar) is its elements', and `d = new[2]`
// on a dynamic array of handles sizes the array (TryQueueBlockingAssign)
// rather than constructing an object, so a target that holds an array's shape
// is no handle to construct into. Whether `name` holds one: a fixed-size or
// dynamic array's, a queue's or an associative array's.
static bool NameHoldsAnArray(std::string_view name, SimContext& ctx) {
  return ctx.FindArrayInfo(name) != nullptr || ctx.FindQueue(name) != nullptr ||
         ctx.FindAssocArray(name) != nullptr;
}

bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs) return false;
  std::string_view target = ClassNewTargetKey(stmt->lhs, arena);
  if (target.empty()) return false;
  auto type_name = ctx.GetVariableClassType(target);
  if (type_name.empty()) return false;
  // Asked ahead of the array paths (TryDispatchSpecialBlockingAssign in
  // statement_assign_core.cpp), this took a module's `C d[]; d = new[2];`
  // for a construction: a C was built by the size, its handle written into
  // the array's carrier, and the array never sized.
  if (NameHoldsAnArray(target, ctx)) return false;

  if (TryClassCopyNewAssign(stmt, target, ctx, arena)) return true;

  if (type_name == "weak_reference") {
    AssignWeakReferenceNew(stmt, target, ctx, arena);
    return true;
  }

  auto handle =
      EvalClassNew(type_name, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  auto* var = ctx.FindVariable(target);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  ApplyClassParamOverrides(target, handle.ToUint64(), ctx, arena);
  return true;
}

bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->rhs->rhs || stmt->rhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (stmt->rhs->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(stmt->rhs->lhs->text);
  if (!cls) return false;
  // §8.25: a parameterized class scope (E#(.N(77))::new) carries its
  // specialization overrides in the base identifier's elements. Bind them as
  // locals in a fresh scope before constructing so the constructor body reads
  // the overridden parameter values, mirroring the class-scope method path.
  bool parameterized = !stmt->rhs->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, stmt->rhs->lhs, ctx, arena);
  }
  auto handle = EvalClassNew(stmt->rhs->lhs->text, nullptr, ctx, arena,
                             stmt->rhs->range.start);
  if (parameterized) ctx.PopScope();
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  return true;
}

// The class whose property `field = new` names, and the object holding the
// property: the declared class of the variable `base` when it is a class
// handle, with the object the handle refers to, and otherwise, when `base` is
// itself a class name and the class has a static property of that name, the
// class alone -- §8.9's `C::x` form, which §8.7 gives the same right to a bare
// `new` as any other target. A null class when the base is neither.
struct MemberNewBase {
  const ClassTypeInfo* cls = nullptr;
  const ClassObject* obj = nullptr;
};

static MemberNewBase MemberNewBaseClass(const Expr* base_expr,
                                        std::string_view field, SimContext& ctx,
                                        Arena& arena) {
  std::string_view base = base_expr->text;
  auto base_type = ctx.GetVariableClassType(base);
  if (!base_type.empty()) {
    const Variable* var = ctx.FindVariable(base);
    const ClassObject* obj =
        var != nullptr ? ctx.GetClassObject(var->value.ToUint64()) : nullptr;
    return {ctx.FindClassType(base_type), obj};
  }
  const auto* cls = ctx.FindClassType(base);
  if (cls == nullptr) {
    // §8.9 with §8.4: the base may be a static property holding a handle,
    // `m_t_inst.m_tw_cb_q = new` in a static method of its class, or any
    // other name a handle is read from; the object it refers to gives the
    // class. Taken for a variable or a class name alone, the static handle
    // named neither and the `new` was read as a value.
    const ClassObject* obj =
        ctx.GetClassObject(EvalExpr(base_expr, ctx, arena).ToUint64());
    return obj != nullptr ? MemberNewBase{obj->type, obj} : MemberNewBase{};
  }
  // §8.13 (printed pages 189-190): `D::m_inst = new` names the static handle
  // a base of D declares, constructed and stored on that class's one storage
  // (ClassTypeInfo::StaticPropertyDeclarer); asked of D's own
  // static_properties, the assignment was declined and the handle stayed
  // null.
  const ClassTypeInfo* declarer = cls->StaticPropertyDeclarer(field);
  if (declarer == nullptr) return {};
  return {declarer, nullptr};
}

// §8.4 / §8.12: `obj.field = new` where field is a class handle, and §8.9's
// `C::field = new` where field is a static class handle of C. The bare `new`
// carries no type context, so resolve field's declared class type from the AST,
// construct the object, and store the resulting handle through the member chain
// (WriteStructField reaches the real nested handle, so a later shallow copy
// shares it rather than falling back to a flat "field.x" key, and reaches the
// class's own storage for the static form).
bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs->lhs || stmt->lhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->lhs->rhs || stmt->lhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  MemberNewBase base =
      MemberNewBaseClass(stmt->lhs->lhs, stmt->lhs->rhs->text, ctx, arena);
  if (base.cls == nullptr) return false;
  // §8.25: a property declared with a type parameter of the class, `T obj`,
  // is a handle of the class the object's specialization binds T to.
  auto field_type =
      PropertyClassName(base.obj, base.cls, stmt->lhs->rhs->text, ctx);
  if (field_type.empty()) return false;
  auto handle =
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  WriteStructField(stmt->lhs, handle, ctx);
  return true;
}

}  // namespace delta
