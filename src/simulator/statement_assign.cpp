#include "simulator/statement_assign.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->base->kind != ExprKind::kIdentifier) return nullptr;
  if (lhs->index_end) return nullptr;
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  // An x or z bit anywhere in the index makes it invalid; an invalid-index
  // write is a no-op, so fail to resolve the element just as an out-of-range
  // index does.
  if (HasUnknownBits(idx)) return nullptr;
  auto elem_name =
      std::string(lhs->base->text) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  // A dimension indexed with an x or z bit is invalid; refuse to build a name
  // for it so the surrounding write resolves to nothing and is a no-op.
  if (HasUnknownBits(idx_val)) return false;
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

// The name of the identifier a compound indexed name stands on, `a` for
// `a[i][j]`, or empty where the chain does not stand on one.
std::string_view CompoundRootName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return (e != nullptr && e->kind == ExprKind::kIdentifier)
             ? e->text
             : std::string_view{};
}

// Whether the outermost index of a compound name lies outside the extent the
// array's ArrayInfo records for the dimension that name it. Only that dimension
// is asked: it is the one every such array has recorded, and a dimension the
// info does not describe cannot say the index is invalid.
static bool OutermostIndexIsOutOfRange(const Expr* lhs, const ArrayInfo& info,
                                       SimContext& ctx, Arena& arena) {
  const Expr* outer = lhs;
  while (outer->base != nullptr && outer->base->kind == ExprKind::kSelect)
    outer = outer->base;
  if (outer->index == nullptr) return false;
  auto idx = EvalExpr(outer->index, ctx, arena);
  if (HasUnknownBits(idx)) return true;
  auto value = idx.ToUint64();
  return value < info.lo || value >= static_cast<uint64_t>(info.lo) + info.size;
}

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena, bool* absent_element) {
  if (absent_element != nullptr) *absent_element = false;
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  if (auto* var = ctx.FindVariable(compound)) return var;
  const ArrayInfo* info = ctx.FindArrayInfo(CompoundRootName(lhs));
  // §7.4.5: "Writing to an array with an invalid index shall perform no
  // operation, with the exceptions of writing to element [$+1] of a queue
  // (described in 7.10.1) and creating a new element of an associative array
  // (described in 7.8.6)" -- and neither exception is an indexed name of this
  // shape, both being reached by their own writers before this one. The caller
  // is told rather than left to fall through, because the fallback resolution
  // walks the name down to the array's base carrier and would write a bit of
  // that instead.
  if (info != nullptr && OutermostIndexIsOutOfRange(lhs, *info, ctx, arena)) {
    if (absent_element != nullptr) *absent_element = true;
    return nullptr;
  }
  // The index is one the array holds, or one no recorded extent contradicts:
  // §7.4.4's dimensions may be "defined in stages with typedef", and only the
  // range the declaration itself wrote is recorded, so a second index of such
  // an array is answered by no extent at all and the element is materialized
  // here. It takes the array's own element width rather than a fixed 32 --
  // WriteVar sizes the value to the cell -- and the scope the write happens in,
  // so a name §23.9 keeps inside an instance can be read back where it was
  // written.
  uint32_t width = info != nullptr ? info->elem_width : 32;
  auto& name = *arena.Create<std::string>(std::move(compound));
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindVariable(lhs->text);
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    auto resolved = StripRootPrefix(name);
    return ctx.FindVariable(resolved);
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

// Checks the tagged-union tag against the field being written. Returns true
// (with an emitted error) when the write targets a member that does not match
// the union's current tag; the caller treats that as a handled no-op write.
// `loc` is where the target was written: the names arrive as text rebuilt from
// the target expression, which carries the position they lost.
static bool TaggedUnionTagMismatch(std::string_view base_name,
                                   std::string_view field_name, SimContext& ctx,
                                   SourceLoc loc) {
  auto tag = ctx.GetVariableTag(base_name);
  if (tag.empty()) return false;
  auto top = field_name;
  auto subdot = top.find('.');
  if (subdot != std::string_view::npos) top = top.substr(0, subdot);
  if (tag == top) return false;
  ctx.GetDiag().Error(
      loc,
      "run-time error: assigning member '" + std::string(field_name) +
          "' of tagged union '" + std::string(base_name) +
          "' which currently has tag '" + std::string(tag) + "'",
      Subclause("11.9"));
  return true;
}

// Writes `field` onto class object `obj`, honoring declared-type scoping
// (§8.15) when the type is known so a base field is written rather than a
// shadowing derived one.
// The declaring type is found by the walk SetPropertyForType makes for the same
// name, because a property declared on a base class is not in a derived type's
// own list.
static const ClassTypeInfo::PropertyInfo* FindPropertyInfo(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return &prop;
    }
  }
  return nullptr;
}

// §7.2.1: the window of a class property's value that a member path names, and
// whether the path names one. `c.p.b` selects a member of the structure the
// property `p` holds -- §6.8 has the property store that structure as one value
// -- so the path resolves to a run of bits of `p` rather than to a property of
// its own. The layout is a fact about the declared type, which
// SimContext::FindStructType answers by the name the declaration wrote; a
// property whose type has no name of its own, or names something that is not an
// aggregate, has no window and the caller keeps the arm it had.
PropertyFieldWindow ResolveClassPropertyField(const ClassTypeInfo* type,
                                              std::string_view path,
                                              SimContext& ctx) {
  PropertyFieldWindow window;
  auto dot = path.find('.');
  if (type == nullptr || dot == std::string_view::npos) return window;
  auto first = path.substr(0, dot);
  const auto* prop = FindPropertyInfo(type, first);
  if (prop == nullptr || prop->type_name.empty()) return window;
  const StructTypeInfo* info = ctx.FindStructType(prop->type_name);
  if (info == nullptr) return window;
  if (!ResolveStructFieldPath(info, path.substr(dot + 1), &window.bit_offset,
                              &window.width)) {
    return window;
  }
  window.property = first;
  window.valid = true;
  return window;
}

Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena) {
  // §6.8 makes a variable "an abstraction of a data storage element" that
  // "shall store a value from one assignment to the next", and §8.7 makes a
  // property one: "each property declared in the class shall be initialized to
  // its explicit default value or its uninitialized value if no default is
  // provided". A property and the variable an initializer read are two storage
  // elements; nothing has to forbid their sharing one buffer for a write
  // through the sharing to be wrong. A by-value `Logic4Vec` parameter reads as
  // though it already owned its bits and does not -- copying one copies the
  // words pointer and not the words -- and that is the trap this site sets.
  //
  // So the copy is taken on entry, above every exit. It used to wrap the
  // conversion below, which covered the coercion but not the two early returns
  // over it, and those are the returns a whole family of declarations takes:
  // CollectClassMembers sizes a property by EvalTypeWidth against an empty
  // typedef map, so a property declared by a typedef name, a class handle, a
  // string, an event or a virtual interface has width_is_declared false, and
  // `pair_t snap = s;` was handed back the module variable's own vector. A
  // packed-member deposit into that variable then wrote through the property,
  // since DepositBitField writes the words it finds rather than replacing
  // them. The prop == nullptr arm is covered by the same move: SetClassField
  // reaches it on a flattened chained-path key.
  //
  // Nothing can ask a Logic4Vec whether it owns its words, so the copy is
  // unconditional and is merely redundant where the conversion allocates
  // anyway. What OwnRhsWords restores beside the words matters more here than
  // it did below: a string property is one of the types that reaches the early
  // return, and ExtractBitField builds with MakeLogic4Vec, which leaves
  // is_string false.
  val = OwnRhsWords(val, arena);
  const auto* prop = FindPropertyInfo(type, name);
  if (prop == nullptr || !prop->width_is_declared) return val;
  // ConvertRealForKnownLhs rather than ResizeToWidth: §6.12.1 converts a value
  // crossing the real boundary rather than reinterpreting its bits, and it
  // resizes everything that does not cross it.
  //
  // §6.11.2 has the coercion below convert "any unknown or high-impedance bits
  // ... to zeros", and it writes in place, so it has to land on the property's
  // own value rather than on the variable the caller read. The copy above is
  // what makes that so, whether or not the conversion allocated: its tail is a
  // ResizeToWidth that hands its argument back untouched at a matching width,
  // which is precisely the case the sharing arose in.
  val = ConvertRealForKnownLhs(val, prop->is_real, prop->width, arena);
  if (!prop->is_4state && !prop->is_real) CoerceTo2State(val);
  // §6.11.3: the declaration's signedness belongs to the value stored in the
  // property. A variable keeps it on the Variable and a read consults it there;
  // a property is only its Logic4Vec, so a value that arrived signed would stay
  // signed in an unsigned property -- the signed literal 240 truncated into a
  // `bit [7:0]` reading -16 rather than 240.
  if (!prop->is_real) val.is_signed = prop->is_signed;
  return val;
}

static void SetClassField(ClassObject* obj, const ClassTypeInfo* declared_type,
                          std::string_view field, const Logic4Vec& rhs_val,
                          Arena& arena) {
  // A chained path that fell back to a flattened key names no property, so
  // FindPropertyInfo answers for none and the value is stored as it arrived.
  const ClassTypeInfo* start = declared_type ? declared_type : obj->type;
  Logic4Vec stored = CoerceToPropertyType(start, field, rhs_val, arena);
  if (declared_type)
    obj->SetPropertyForType(field, declared_type, stored);
  else
    obj->SetProperty(std::string(field), stored);
}

// Walks a (possibly chained) field path down to the object that holds its last
// field. A chained path `first.rest` (e.g. `a.val`) fetches `first` as a class
// handle and descends into the referenced object, so `o2.a.val = 88` reaches
// the same Inner object shared by a shallow copy (§8.12) rather than naming a
// flat "a.val" key on the outer object. Mirrors ResolveClassFieldChain on the
// read side; the inner fields carry no declared-type shadowing context. When
// `first` is not a live handle, the whole remaining path stays with the object
// in hand and is stored under a flattened key (the legacy nested-handle storage
// scheme).
static FieldTarget ResolveClassFieldTarget(ClassObject* obj,
                                           const ClassTypeInfo* declared_type,
                                           std::string_view field_path,
                                           SimContext& ctx) {
  auto dot = field_path.find('.');
  if (dot != std::string_view::npos) {
    auto& arena = ctx.GetArena();
    auto first = field_path.substr(0, dot);
    Logic4Vec handle_val =
        declared_type ? obj->GetPropertyForType(first, declared_type, arena)
                      : obj->GetProperty(first, arena);
    if (auto* next_obj = ctx.GetClassObject(handle_val.ToUint64())) {
      return ResolveClassFieldTarget(next_obj, nullptr,
                                     field_path.substr(dot + 1), ctx);
    }
    // §7.2.1: `first` holds a structure rather than a handle, so the rest of
    // the path selects a member of it. The flattened key below would store the
    // value under a name the class never declared and leave the property the
    // path actually names untouched.
    PropertyFieldWindow window = ResolveClassPropertyField(
        declared_type ? declared_type : obj->type, field_path, ctx);
    if (window.valid) {
      FieldTarget bits;
      bits.kind = FieldTarget::Kind::kPropertyBits;
      bits.obj = obj;
      bits.type = declared_type;
      bits.field = std::string(window.property);
      bits.bit_offset = window.bit_offset;
      bits.width = window.width;
      return bits;
    }
  }
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = obj;
  target.type = declared_type;
  target.field = std::string(field_path);
  return target;
}

// The field of the class object base_var refers to. Answers a kNone target when
// the handle refers to no live object, which is the base that names no storage.
static FieldTarget ResolveClassObjectField(Variable* base_var,
                                           std::string_view base_name,
                                           std::string_view field_name,
                                           SimContext& ctx) {
  auto* obj = ctx.GetClassObject(base_var->value.ToUint64());
  if (!obj) return {};
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ctx.GetVariableClassType(base_name);
  if (!declared.empty()) declared_type = ctx.FindClassType(declared);
  FieldTarget target =
      ResolveClassFieldTarget(obj, declared_type, field_name, ctx);
  target.notify = base_var;
  return target;
}

// The field of the current `this` object. *handled is set true when base_name
// names `this`; the target answered is then the whole answer.
static FieldTarget ResolveThisField(std::string_view base_name,
                                    std::string_view field_name,
                                    SimContext& ctx, bool* handled) {
  *handled = false;
  if (base_name != "this") return {};
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (!self) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = self;
  target.field = std::string(field_name);
  return target;
}

// The field of the parent slice of the current `this` object, reached through
// `super`. *handled is set true when base_name names `super`.
static FieldTarget ResolveSuperField(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, bool* handled) {
  *handled = false;
  if (base_name != "super") return {};
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (!(self && self->type && self->type->parent)) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = self;
  target.type = self->type->parent;
  target.field = std::string(field_name);
  return target;
}

// The static property field_name of the class named base_name. *handled is set
// true when base_name names a known class type.
static FieldTarget ResolveStaticClassField(std::string_view base_name,
                                           std::string_view field_name,
                                           SimContext& ctx, bool* handled) {
  *handled = false;
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return {};
  *handled = true;
  auto sit = cls_type->static_properties.find(std::string(field_name));
  if (sit == cls_type->static_properties.end()) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kStatic;
  target.type = cls_type;
  target.slot = &sit->second;
  target.field = std::string(field_name);
  return target;
}

// The component field_name of the interface instance the virtual interface
// variable base_name is bound to. §25.9: "Once a virtual interface has been
// initialized, all the components of the underlying interface instance are
// directly available to the virtual interface via the dot notation. These
// components can only be used in procedural statements", and an assignment is
// such a statement -- the clause's own example writes `bus.req <= 1'b1`. The
// component belongs to the instance, so the path names that instance's own
// variable and the write lands there.
//
// One arm serves both assignment forms, because both reach here: the blocking
// one through WriteStructField, which resolves and deposits at the one moment,
// and the nonblocking one through ScheduleFieldNba, which asks this alone when
// the statement executes and defers only the deposit. That is also where
// §10.4.2 wants a "virtual interface reference" in an lvalue evaluated, "at the
// same time as the expression on the right-hand side", so the binding read
// here is the one in force when the statement ran, not the one in the update
// region.
//
// *handled is set true when base_name names a virtual interface variable,
// bound or not. An unbound one is the null reference §25.9 makes a runtime
// error -- the same one a read through it raises -- reported here and resolved
// to storage that takes no value, so the caller sees a handled path rather
// than an unwritten one it would report again or drop in silence.
static FieldTarget ResolveVirtualInterfaceField(std::string_view base_name,
                                                std::string_view field_name,
                                                SimContext& ctx, SourceLoc loc,
                                                bool* handled) {
  *handled = false;
  auto* base_var = ctx.FindVariable(base_name);
  if (!ctx.IsVirtualInterfaceVar(base_var)) return {};
  *handled = true;
  if (!ctx.VirtualInterfaceIsBound(base_var)) {
    ctx.GetDiag().Error(loc, "reference through a null virtual interface",
                        Subclause("25.9"));
    FieldTarget target;
    target.kind = FieldTarget::Kind::kNoOp;
    return target;
  }
  std::string name(ctx.VirtualInterfaceBinding(base_var));
  name += ".";
  name += field_name;
  auto* component = ctx.FindVariable(name);
  if (!component) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kVariable;
  target.var = component;
  return target;
}

// The field field_name of the variable named base_name, which may be a packed
// struct/union or a class-object handle. The caller has confirmed base_name is
// neither this/super nor a class type. `loc` is the position a tagged-union tag
// mismatch is reported at.
static FieldTarget ResolveVariableField(std::string_view base_name,
                                        std::string_view field_name,
                                        SimContext& ctx, SourceLoc loc) {
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return {};
  const auto* info = ctx.GetVariableStructType(base_name);
  if (info) {
    FieldTarget target;
    if (info->is_union &&
        TaggedUnionTagMismatch(base_name, field_name, ctx, loc)) {
      target.kind = FieldTarget::Kind::kNoOp;
      return target;
    }
    if (ResolveStructFieldPath(info, field_name, &target.bit_offset,
                               &target.width)) {
      target.kind = FieldTarget::Kind::kBits;
      target.var = base_var;
      return target;
    }
  }
  return ResolveClassObjectField(base_var, base_name, field_name, ctx);
}

FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx) {
  std::string name;
  BuildLhsName(lhs, name);
  auto dot = name.find('.');
  if (dot == std::string::npos) return {};
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);

  bool handled = false;
  FieldTarget target = ResolveThisField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveSuperField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveStaticClassField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  // A virtual interface base is a plain variable name, so it is asked after
  // the bases that are not -- `this`, `super`, a class type name -- which it
  // would otherwise shadow, and before ResolveVariableField, which would take
  // the virtual interface variable for a packed object or a class handle, find
  // neither, and answer that the path names no storage.
  target = ResolveVirtualInterfaceField(base_name, field_name, ctx,
                                        lhs->range.start, &handled);
  if (handled) return target;
  return ResolveVariableField(base_name, field_name, ctx, lhs->range.start);
}

// Deposits a value in a whole variable, which is the write a component of an
// interface instance takes: it owns all of its storage, so the value is
// resized to the declaration rather than deposited into a window of it. Same
// steps, in the same order, as a direct assignment to that component makes
// (WriteVar and AssignToScalarLhs, statement_assign_core.cpp): §10.6.2 leaves
// a forced variable to its force, a string takes its text, §10.7 resizes the
// value to the declared width, a 2-state declaration drops x and z, and the
// watchers are notified exactly as the direct write notifies them -- a write
// through a virtual interface is the same write, reached by another name.
static void WriteWholeVariable(Variable* var, const Logic4Vec& val,
                               Arena& arena) {
  if (var->is_forced) return;
  if (var->is_string) {
    var->value = StripStringZeros(val, arena);
    var->NotifyWatchers();
    return;
  }
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

void WriteResolvedField(const FieldTarget& target, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena) {
  switch (target.kind) {
    case FieldTarget::Kind::kBits:
      DepositBitField(target.var->value, target.bit_offset, rhs_val,
                      target.width);
      target.var->NotifyWatchers();
      return;
    case FieldTarget::Kind::kVariable:
      WriteWholeVariable(target.var, rhs_val, arena);
      return;
    case FieldTarget::Kind::kProperty:
      SetClassField(target.obj, target.type, target.field, rhs_val, arena);
      // §9.4.2 has a change to "object data members" re-evaluate the event
      // expression, and it says nothing about which syntax named the object.
      // The watchers sit on the variables that designate it, so the object is
      // announced by handle: a path read out of a variable notifies the
      // variable it was read from, and `this` and `super`, which are read off
      // the running process and carry no name at all, notify the same way as
      // every other designator of the same object.
      if (target.notify) target.notify->NotifyWatchers();
      if (target.obj) ctx.NotifyClassHandleWatchers(target.obj->handle);
      return;
    case FieldTarget::Kind::kPropertyBits: {
      // §7.2.1 selects a member of the structure the property holds, so the
      // deposit lands in the property's own bits and the property is stored
      // back whole. A property is only its Logic4Vec, and the value read out of
      // it is the one the object holds, so the copy is taken before the deposit
      // writes into it.
      Logic4Vec held =
          target.type
              ? target.obj->GetPropertyForType(target.field, target.type, arena)
              : target.obj->GetProperty(target.field, arena);
      Logic4Vec updated = OwnRhsWords(held, arena);
      DepositBitField(updated, target.bit_offset, rhs_val, target.width);
      SetClassField(target.obj, target.type, target.field, updated, arena);
      if (target.notify) target.notify->NotifyWatchers();
      if (target.obj) ctx.NotifyClassHandleWatchers(target.obj->handle);
      return;
    }
    case FieldTarget::Kind::kStatic:
      *target.slot =
          CoerceToPropertyType(target.type, target.field, rhs_val, arena);
      return;
    case FieldTarget::Kind::kNone:
    case FieldTarget::Kind::kNoOp:
      return;
  }
}

// §11.5.1 makes a bit-select and a part-select of a vector an lvalue in their
// own right, and §6.8 has the variable behind one store what is assigned to it
// from one assignment to the next. A class property is such a variable -- §8.3
// declares class properties as data declarations -- and `c.p[7:0] = 8'h00` is a
// select whose base is a member access, which every arm of
// TrySelectBlockingAssign declined: each of them names a context variable, and
// the fallback ResolveLhsVariable rebuilds the text "c.p" and asks FindVariable
// for storage that lives in the ClassObject's property map instead, so the
// write was dropped with `true` returned to the caller and nothing reported.
//
// The window is resolved the way §7.8.7's write to bits of an associative
// element resolves its own: a stack Variable lends WriteBitSelect the width and
// state-ness the declaration gave the property, since a property is stored as a
// bare vector carrying neither, and the value it leaves is stored back through
// the same coercion and the same announcement a whole-property write takes.
// A property whose width the collector could not size -- a typedef name, a
// class handle, a string -- is declined rather than addressed through a carrier
// width the declaration never gave.
bool TryWriteClassPropertyBits(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena) {
  if (!lhs || lhs->kind != ExprKind::kSelect || !lhs->base) return false;
  if (lhs->base->kind != ExprKind::kMemberAccess) return false;
  FieldTarget target = ResolveFieldTarget(lhs->base, ctx);
  if (target.kind != FieldTarget::Kind::kProperty || target.obj == nullptr)
    return false;
  const ClassTypeInfo* start = target.type ? target.type : target.obj->type;
  const auto* prop = FindPropertyInfo(start, target.field);
  if (prop == nullptr || !prop->width_is_declared || prop->is_real)
    return false;

  Variable elem;
  elem.value = target.type ? target.obj->GetPropertyForType(target.field,
                                                            target.type, arena)
                           : target.obj->GetProperty(target.field, arena);
  elem.is_4state = prop->is_4state;
  elem.is_signed = prop->is_signed;
  WriteBitSelect(&elem, lhs, rhs_val, ctx, arena);
  SetClassField(target.obj, target.type, target.field, elem.value, arena);
  if (target.notify) target.notify->NotifyWatchers();
  ctx.NotifyClassHandleWatchers(target.obj->handle);
  return true;
}

// The declared width of the storage a resolved field target names, which
// §11.3.6 makes the data type of the value an assignment expression returns:
// "The data type of the value that is returned is the data type of the
// left-hand side." Zero where the target names storage of no declared width --
// a property the collector could not size, a string, an array the path fell
// back to a flattened key on -- which a caller reads as "no answer" and leaves
// the value it has.
static uint32_t FieldTargetWidth(const FieldTarget& target) {
  switch (target.kind) {
    case FieldTarget::Kind::kBits:
      return target.width;
    case FieldTarget::Kind::kVariable:
      return target.var != nullptr ? target.var->value.width : 0;
    case FieldTarget::Kind::kProperty: {
      const ClassTypeInfo* start =
          target.type ? target.type : (target.obj ? target.obj->type : nullptr);
      const auto* prop = FindPropertyInfo(start, target.field);
      return (prop != nullptr && prop->width_is_declared) ? prop->width : 0;
    }
    case FieldTarget::Kind::kPropertyBits:
      return target.width;
    case FieldTarget::Kind::kStatic:
      return target.slot != nullptr ? target.slot->width : 0;
    case FieldTarget::Kind::kNone:
    case FieldTarget::Kind::kNoOp:
      return 0;
  }
  return 0;
}

bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx, uint32_t* written_width) {
  // §7.8.7: `b[2].x = 5` names a member of an associative array element, which
  // the name ResolveFieldTarget builds cannot reach because the select
  // contributes nothing to it. Allocate the element and write the member
  // through the array.
  if (TryWriteAssocMemberField(lhs, rhs_val, ctx, ctx.GetArena())) return true;
  // §10.4.2 has a blocking assignment resolve its target and deposit the value
  // at the one moment, so the two halves are asked back to back here. A
  // nonblocking assignment asks ResolveFieldTarget alone and defers
  // WriteResolvedField to the update region.
  FieldTarget target = ResolveFieldTarget(lhs, ctx);
  if (target.kind == FieldTarget::Kind::kNone) return false;
  // The width is reported from the resolved target rather than measured from
  // the left-hand side by the caller: a member access resolves to a window of a
  // packed variable, a whole component of an interface instance or a class
  // property, and only the resolution tells which.
  if (written_width != nullptr) *written_width = FieldTargetWidth(target);
  WriteResolvedField(target, rhs_val, ctx, ctx.GetArena());
  return true;
}

}  // namespace delta
