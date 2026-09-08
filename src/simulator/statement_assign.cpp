#include "simulator/statement_assign.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
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

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  auto* var = ctx.FindVariable(compound);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(std::move(compound)),
                            32);
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

Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena) {
  const auto* prop = FindPropertyInfo(type, name);
  if (prop == nullptr || !prop->width_is_declared) return val;
  // ConvertRealForKnownLhs rather than ResizeToWidth: §6.12.1 converts a value
  // crossing the real boundary rather than reinterpreting its bits, and it
  // resizes everything that does not cross it.
  //
  // §6.11.2 has the coercion below convert "any unknown or high-impedance bits
  // ... to zeros", and it writes in place, so it has to land on the property's
  // own value rather than on the variable the caller read. §6.8 makes a
  // variable "an abstraction of a data storage element" that "shall store a
  // value from one assignment to the next", and the property and that variable
  // are two of them; nothing has to forbid their sharing one buffer for a write
  // through the sharing to be wrong. A by-value `Logic4Vec` parameter reads as
  // though it already owned its bits and does not -- copying one copies the
  // words pointer and not the words -- and that is the trap this site sets.
  //
  // The copy wraps the conversion rather than following the coercion, which
  // would be a copy of the damage, or sitting inside the conversion, whose tail
  // is a ResizeToWidth that hands its argument back untouched at a matching
  // width -- precisely the case the sharing arises in. Outside, it covers every
  // path and is merely redundant where the conversion allocated anyway.
  val = OwnRhsWords(
      ConvertRealForKnownLhs(val, prop->is_real, prop->width, arena), arena);
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
                        Arena& arena) {
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
      // Only a path read out of a variable notifies, which is where the
      // blocking form notifies; `this` and `super` are read off the process.
      if (target.notify) target.notify->NotifyWatchers();
      return;
    case FieldTarget::Kind::kStatic:
      *target.slot =
          CoerceToPropertyType(target.type, target.field, rhs_val, arena);
      return;
    case FieldTarget::Kind::kNone:
    case FieldTarget::Kind::kNoOp:
      return;
  }
}

bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx) {
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
  WriteResolvedField(target, rhs_val, ctx.GetArena());
  return true;
}

// Deposits `rhs_val` in the window of `var` that `bits` names. §11.5.1 has a
// part-select that is partly out of range "when written, only affect the bits
// that are in range", and which bits of the value the affected ones receive is
// bits.src_lo: a select running off the low end of its object has its own low
// bits land nowhere, so `a[1 -: 4] = 4'b1101` on a `logic [7:0] a` -- which the
// clause reads as `a[1:-2]` -- gives `a[1:0]` the value's bits [3:2] and must
// leave `a` at 8'h03. Taking the value's low bits whichever end the select ran
// off left it at 8'h01. The offset is zero for a select running off the high
// end, where the bits that land are the value's least significant ones.
//
// The window is deposited rather than computed in a machine word, because
// "only affect the bits that are in range" is a statement about every bit of
// the target the select did not name and not only about the ones beside it.
// Reading the target through Logic4Vec::ToUint64 and rebuilding it with
// MakeLogic4VecVal moved three sets of them. ToUint64 returns words[0] alone
// and MakeLogic4VecVal fills a fresh zeroed array, so a target wider than one
// word lost everything above bit 63: `w = '1; w[3:0] = 4'h0;` on a
// `logic [99:0] w` must leave 96 ones and left 60, w[99:64] being neither named
// by the select nor the value's to touch. ToUint64 returns `aval & ~bval` and
// MakeLogic4VecVal sets no bval, so the x and z that §6.3.1 lets every bit of a
// 4-state vector hold -- "All bits of 4-state vectors can be independently set
// to one of the four basic values", and §6.11.2 makes `logic` one of those
// types, whose values "have additional bits, which encode the x and z states"
// -- were read as 0 on the way in and stored as 0 on the way out:
// `a = 8'hxx; a[1:0] = 2'b11;` must read 8'bxxxxxx11 and read 8'b00000011, and
// `a = 8'h00; a[1:0] = 2'b1x;` must read 8'b0000001x and read 8'b00000010. And
// `mask << bits.lo` was undefined once the window began at bit 64 or above, the
// shift count being taken modulo 64 on x86-64, so `w[71:68] = 4'hF` on the same
// `logic [99:0] w` landed on w[7:4] and left w[71:68] at zero. DepositBitField
// is documented multi-word safe for a start bit of 64 or more, which answers
// the shift and the lost high words at once, and ExtractBitField takes the
// value's landing bits with their 4-state encoding kept, which answers the
// projection on the source side and makes bits.src_lo simply where the extract
// begins.
//
// The deposit is made into a fresh copy of the target's current value rather
// than through the words it is holding, for the reason WriteOwnedBits
// (statement_assign_decl.cpp) gives: copying a Logic4Vec copies its `words`
// pointer rather than the words (common/types.h), so a variable last written
// whole from another object shares that object's storage and an in-place
// deposit would write these bits into whatever else is holding it.
//
// §6.11.2 makes `bit` and `int` 2-state types that "do not have unknown
// values", so a 2-state target is coerced here explicitly. MakeLogic4VecVal
// gave that for free by never setting a bval; now that the deposit carries x
// and z, an x reaching such a target would otherwise survive.
void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena) {
  Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
  DepositBitField(updated, bits.lo,
                  ExtractBitField(arena, rhs_val, bits.src_lo, bits.width),
                  bits.width);
  var->value = updated;
  if (!var->is_4state) CoerceTo2State(var->value);
}

PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena) {
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return {0, 0};
  auto idx = SelectBoundValue(idx_val);
  if (sel->index_end == nullptr) {
    // §7.4.1: a single index on a packed multidimensional array addresses an
    // outermost element -- the inner dimensions' width -- rather than one bit,
    // and addresses it whole or not at all, so the source offset stays zero.
    if (var.packed_elem_width > 1) {
      PackedRange elems = var.DeclaredRange();
      if (!elems.Contains(idx)) return {0, 0};
      auto base = static_cast<uint32_t>(elems.OffsetOf(idx));
      return {base * var.packed_elem_width, var.packed_elem_width};
    }
    PackedRange range = var.BitSelectRange();
    if (!range.Contains(idx)) return {0, 0};
    return {static_cast<uint32_t>(range.OffsetOf(idx)), 1};
  }
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return {0, 0};
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end_val),
                                        sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  // §11.5.1 spells an indexed part-select's width out separately and requires
  // that it "shall be a positive constant", so a width of zero names no bit of
  // the object -- which is what a zero width from this function already means.
  // The pair PartSelectTargetIndices answers cannot say so on its own: it is
  // the two ends of a width the select does not have, and for `a[3 +: 0]` it is
  // the indices 3 and 2, which any declaration holding them resolves to the
  // two-bit window a[3:2]. The write path reports that width as an error ahead
  // of this call, in ReportZeroWidthPartSelect below; every caller reads the
  // zero this returns as the absence it is.
  if (target.declared_width == 0) return {0, 0};
  return PartSelectStorageBits(var.BitSelectRange(), target.first,
                               target.second);
}

// Whether two stored values differ, which is what the notification in
// WriteBitSelect turns on. It is the comparison EventAwaiter::CheckEdge makes
// for a non-edge event (awaiters_event_control.h) and the one the VCD writer
// makes to decide a transition (eval_system_task_dump.cpp), written out again
// here rather than shared with either, so that this file's own answer to
// §9.4.2's "change in the result of the expression" needs nothing from theirs.
static bool StoredBitsDiffer(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return true;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return true;
  }
  return false;
}

// §11.5.1's report for a select written with a width of zero, which is the one
// answer the resolution below cannot give: SelectStorageBits returns an empty
// window for it, and returns the same empty window for an unknown index, an
// out-of-range index and a select landing on no bit of the object, all of which
// the clause leaves silent. The width belongs to the select as written rather
// than to the object it addresses -- §11.5.1 requires it to "be a positive
// constant" -- so it is read on its own, from a base of zero, which is the
// declared width PartSelectTargetIndices gives either indexed form whatever the
// base is. Only those two forms carry a width, so `a[7:0]` reads nothing twice.
void ReportZeroWidthPartSelect(const Expr* sel, SimContext& ctx, Arena& arena) {
  if (!sel->index_end) return;
  if (!sel->is_part_select_plus && !sel->is_part_select_minus) return;
  auto width = SelectBoundValue(EvalExpr(sel->index_end, ctx, arena));
  auto target = PartSelectTargetIndices(0, width, sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  if (target.declared_width != 0) return;
  ctx.GetDiag().Error(sel->range.start, "zero-width part-select is not allowed",
                      Subclause("11.5.1"));
}

// The write itself, which §11.5.1 states as two questions this file now answers
// once each. "The actual bit that is accessed by an address is, in part,
// determined by the declaration" is the resolution, and SelectStorageBits
// answers it; a part-select partly out of range "shall, when written, only
// affect the bits that are in range" is the deposit, and WritePartSelect
// answers that. This function walked the same four arms a second time with the
// write attached -- the shape a correction lands on one of and not the other,
// as #3532 records on the nonblocking path, and one copy-paste-test cannot see,
// the two walks being an early-returning writer against a value-returning
// resolver rather than duplicated text. The bit-select goes with them, being
// the one-bit case of that window rather than a write of its own: computed in a
// machine word instead, `uint64_t{1} << off` was undefined for a bit at 64 or
// above, and `enable[64] = 1'b1;` on a `logic [64:0] enable` set enable[0].
//
// The packed arm's write carried one test the resolver has no counterpart for,
// `off < var->value.width`, and it is dropped rather than moved into
// SelectStorageBits. RecordPackedRange (lowerer_register.cpp) records a
// declared range only once its span times the element width equals value.width,
// so an index that range contains has its element wholly inside the value, and
// where the two disagree there is no declared range at all, only the implicit
// [width-1:0] one. DepositBitField answers both, breaking at the first bit at
// or past dst.width -- that same "only affect the bits that are in range" -- so
// an element past the value deposits none of itself. Only a read needs the test
// (TryPackedElementSelect, eval_select.cpp), owing a value where a write that
// lands nowhere owes nothing.
//
// Nothing here says anything about the notification, which WriteBitSelect
// decides from the stored value once this returns.
static void WriteBitSelectBits(Variable* var, const Expr* lhs,
                               const Logic4Vec& rhs_val, SimContext& ctx,
                               Arena& arena) {
  ReportZeroWidthPartSelect(lhs, ctx, arena);
  PartSelectBits bits = SelectStorageBits(*var, lhs, ctx, arena);
  if (bits.width == 0) return;
  WritePartSelect(var, bits, rhs_val, arena);
}

// Writes the window of `var` that `lhs` names, and wakes `var`'s watchers when
// that write moved the value.
//
// The notification is made here rather than by the callers because each of the
// five call sites had to remember the rule for itself, and they did not agree:
// #3521 is the record of one forgetting the notification entirely, and #3522
// the record of the four that remembered it remembering it in a form too
// coarse -- an unconditional NotifyWatchers() after a call that returns having
// written nothing down six separate paths. §9.4.2 closes with "A change of
// value in any operand of the expression without a change in the result of the
// expression shall not be detected as an event", so a statement that stored no
// bit owes no event at all: §11.5.1 gives an out-of-range write "no effect on
// the data stored when written", yet `a[9] = 1'b1;` on a `logic [7:0] a` ran an
// `always_comb` block reading `a` a third time.
//
// This function is the only one holding both the value before the write and the
// value after it, and "a change in the result" can only be measured between
// those two. The baseline is a Logic4Snapshot rather than a Logic4Vec copy
// because a Logic4Vec copied from `value` shares `value`'s words -- the copy
// takes the `words` pointer (common/types.h) -- so the deposit below would
// write through the baseline as well, the two sides of the comparison would be
// one value, and no change would ever be seen. That is #3358, and it is why
// Variable::prev_value is a snapshot too.
//
// A bool returned by the writer would not have been enough. It says "I wrote",
// not "the value changed", and those part company: `a[3] = 1'b1;` on a bit
// already 1 takes a writing path all the way to the deposit and changes
// nothing, which §9.4.2's last sentence is precisely about.
//
// The comparison sits at the end rather than beside the deposit, because the
// deposit is not where the paths end: the window WriteBitSelectBits resolves is
// empty for an unknown index, an out-of-range index, a zero declared width and
// a select landing on no bit of the object, and it returns having written
// nothing down every one of them. Reading the stored value once, after the
// write, is blind to which path ran.
void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  // §10.6.2: a force "shall override a procedural assignment ... until a
  // release procedural statement is executed on the variable". Naming a
  // bit-select or a part-select as the target does not take the statement out
  // of that class -- the clause's own "shall not be a bit-select or a
  // part-select of a variable" restricts what may be forced, not what a force
  // overrides -- so this declines as every whole-variable writer does. It is
  // the one place the statement form, the compound form, the increment, the
  // expression forms and the subroutine-body form all pass through. It declines
  // ahead of the snapshot, as WriteVar (statement_assign_core.cpp) declines
  // ahead of its own notification: nothing is written, so there is nothing to
  // compare and nobody to wake.
  if (var->is_forced) return;
  Logic4Snapshot before;
  before.Capture(var->value);
  WriteBitSelectBits(var, lhs, rhs_val, ctx, arena);
  if (StoredBitsDiffer(before.Get(), var->value)) var->NotifyWatchers();
}

// Single-word resize for known (no x/z) values that fit in 64 bits, applying
// sign extension when the source is signed and being widened.
// Logic4Vec::is_signed carries the signedness §11.7 gives the value itself,
// which $signed and $unsigned set, so the result takes the flag from val
// instead of the false MakeLogic4VecVal leaves in place. ResizeToWidth sets
// that flag from val on its wide path, and a value resized here is stored
// beside those, so the two paths have to answer alike.
static Logic4Vec ResizeNarrowKnown(const Logic4Vec& val, uint32_t target_width,
                                   Arena& arena) {
  uint64_t v = val.ToUint64();
  if (val.is_signed && target_width > val.width && val.width > 0 &&
      val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (v & sign_bit) v |= ~uint64_t{0} << val.width;
  }
  Logic4Vec result = MakeLogic4VecVal(arena, target_width, v);
  result.is_signed = val.is_signed;
  return result;
}

// Replicates the source MSB across the widened high bits of result when val is
// signed and being widened past its original width.
static void SignExtendWideResult(const Logic4Vec& val, uint32_t target_width,
                                 Logic4Vec& result) {
  if (!val.is_signed || target_width <= val.width || val.width == 0) return;
  uint32_t msb_idx = (val.width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((val.width - 1) % 64);
  uint64_t a_fill = (val.words[msb_idx].aval & msb_mask) ? ~uint64_t{0} : 0;
  uint64_t b_fill = (val.words[msb_idx].bval & msb_mask) ? ~uint64_t{0} : 0;
  if (!(a_fill || b_fill)) return;
  uint32_t fill_bit = val.width % 64;
  if (fill_bit != 0) {
    uint64_t fill_mask = ~((uint64_t{1} << fill_bit) - 1);
    uint32_t target_bits_in_word = target_width % 64;
    if (target_bits_in_word > fill_bit) {
      uint64_t upper_limit = (uint64_t{1} << target_bits_in_word) - 1;
      fill_mask &= upper_limit;
    }
    result.words[val.width / 64].aval |= a_fill & fill_mask;
    result.words[val.width / 64].bval |= b_fill & fill_mask;
  }
  uint32_t first_full = val.width / 64 + (fill_bit != 0 ? 1 : 0);
  for (uint32_t i = first_full; i < result.nwords; ++i) {
    result.words[i].aval = a_fill;
    result.words[i].bval = b_fill;
  }
}

// Clears any bits above target_width in the final (partial) word of result.
static void MaskHighBits(uint32_t target_width, Logic4Vec& result) {
  uint32_t last_bit = target_width % 64;
  if (last_bit == 0) return;
  uint32_t last_word = (target_width - 1) / 64;
  uint64_t mask = (uint64_t{1} << last_bit) - 1;
  result.words[last_word].aval &= mask;
  result.words[last_word].bval &= mask;
}

Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena) {
  if (val.width == target_width || target_width == 0) return val;

  bool has_xz = false;
  for (uint32_t i = 0; i < val.nwords && !has_xz; ++i)
    has_xz = val.words[i].bval != 0;

  if (!has_xz && val.width <= 64 && target_width <= 64)
    return ResizeNarrowKnown(val, target_width, arena);

  auto result = MakeLogic4Vec(arena, target_width);
  result.is_signed = val.is_signed;
  uint32_t copy_words = std::min(val.nwords, result.nwords);
  for (uint32_t i = 0; i < copy_words; ++i) {
    result.words[i].aval = val.words[i].aval;
    result.words[i].bval = val.words[i].bval;
  }
  SignExtendWideResult(val, target_width, result);
  MaskHighBits(target_width, result);
  return result;
}

void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx) {
  uint32_t n = std::min(dst.size, src.size);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t si =
        src.is_descending ? (src.lo + src.size - 1 - i) : (src.lo + i);
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto sn = std::string(src_name) + "[" + std::to_string(si) + "]";
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* sv = ctx.FindVariable(sn);
    auto* dv = ctx.FindVariable(dn);
    if (sv && dv) {
      dv->value = sv->value;
      dv->NotifyWatchers();
    }
  }
}

}  // namespace delta
