#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_event_property.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/clocking.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/eval_struct_property.h"
#include "simulator/evaluation.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/virtual_interface.h"

namespace delta {

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  out.loc = access->rhs->range.start;
  return true;
}

struct ReplicateInner {
  uint64_t aval = 0;
  uint64_t bval = 0;
  uint32_t width = 0;
  bool is_string = false;
};

static ReplicateInner EvalReplicateInner(const Expr* expr, SimContext& ctx,
                                         Arena& arena) {
  ReplicateInner inner;
  std::vector<Logic4Vec> parts;
  // §11.4.12.1: the inner expression of a replication is self-determined, an
  // unbased unsized literal among its operands one bit wide (§5.7.1).
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    if (parts.back().is_string) inner.is_string = true;
    inner.width += parts.back().width;
  }
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    // Replication copies the operand's bits verbatim, so preserve the raw
    // 4-state encoding; ToUint64() would project unknown bits to 0.
    uint64_t av = (it->nwords > 0) ? it->words[0].aval : 0;
    uint64_t bv = (it->nwords > 0) ? it->words[0].bval : 0;
    inner.aval |= av << bit_pos;
    inner.bval |= bv << bit_pos;
    bit_pos += it->width;
  }
  return inner;
}

Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, arena).ToUint64());
  if (count == 0) {
    EvalReplicateInner(expr, ctx, arena);
    return MakeLogic4Vec(arena, 0);
  }
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);

  auto inner = EvalReplicateInner(expr, ctx, arena);
  uint32_t total_width = inner.width * count;
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  uint32_t ew = (inner.width > 64) ? 64 : inner.width;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= inner.aval << bit;
      result.words[word].bval |= inner.bval << bit;
      if (bit + ew > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= inner.aval >> (64 - bit);
        result.words[word + 1].bval |= inner.bval >> (64 - bit);
      }
    }
    bit_pos += inner.width;
  }
  result.is_string = inner.is_string;
  return result;
}

static bool TryCollectionAccess(std::string_view base, std::string_view field,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalArrayProperty(base, field, ctx, arena, out)) return true;
  if (TryExecArrayPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalQueueProperty(base, field, ctx, arena, out)) return true;
  if (TryExecQueuePropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalAssocProperty(base, field, ctx, arena, out)) return true;
  if (TryExecAssocPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalStringProperty(base, field, ctx, arena, out)) return true;
  return false;
}

// Bundles the subject of a member access (`base_name.field_name`) together with
// the resolved base variable (when one exists), the evaluation context and the
// position the access was written at. A single instance is built once in
// ResolveMemberByType and shared across the per-feature member-access helpers
// below. The name is rebuilt from the expression before the helpers run and no
// longer points back at it, so the position is carried here rather than
// recovered: it is what a report from one of those helpers names.
struct MemberAccess {
  std::string_view base_name;
  std::string_view field_name;
  Variable* base_var;
  SimContext& ctx;
  Arena& arena;
  SourceLoc loc;
};

// Reads field `field` from class object `obj`, honoring declared-type scoping
// (§8.15) when `declared_type` is known so a base method reads a shadowed base
// field rather than the derived one.
static Logic4Vec ReadClassField(ClassObject* obj,
                                const ClassTypeInfo* declared_type,
                                std::string_view field, Arena& arena) {
  if (declared_type)
    return obj->GetPropertyForType(field, declared_type, arena);
  return obj->GetProperty(field, arena);
}

// Resolves a (possibly chained) field path against class object `obj`. A single
// field is read directly. A chained path `first.rest` (e.g. `a.next.data` for a
// forward-typedef linked list, §6.18) fetches `first` as a class handle and
// recurses into the referenced object; the inner fields carry no declared-type
// shadowing context, so they are read by bare name. When `first` does not name
// a live class handle, the chain falls back to reading the whole dotted path as
// a single flattened key on `obj` (the legacy nested-handle storage scheme).
Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path, SimContext& ctx,
                                 Arena& arena) {
  auto dot = field_path.find('.');
  if (dot == std::string_view::npos) {
    return ReadClassField(obj, declared_type, field_path, arena);
  }
  auto first = field_path.substr(0, dot);
  auto rest = field_path.substr(dot + 1);
  Logic4Vec handle_val = ReadClassField(obj, declared_type, first, arena);
  // §7.2.1: `first` declared with a structure's type holds that structure
  // rather than a handle, so the rest of the path selects a member of the
  // value just read. Asked before the handle lookup, because a structure
  // whose bits happen to equal a live handle's number is still a structure.
  // The flattened key below names a property the class never declared, which
  // answers what an earlier write to the same path left there and a known
  // zero where there was none.
  PropertyFieldWindow window = ResolveClassPropertyField(
      declared_type ? declared_type : obj->type, field_path, ctx);
  if (window.valid) {
    return MemberValueOf(
        ExtractBitField(arena, handle_val, window.bit_offset, window.width),
        window.member_kind, arena);
  }
  auto* next_obj = ctx.GetClassObject(handle_val.ToUint64());
  if (!next_obj) return ReadClassField(obj, declared_type, field_path, arena);
  return ResolveClassFieldChain(next_obj, nullptr, rest, ctx, arena);
}

static bool TryClassPropertyAccess(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  if (!base_var) return false;
  auto* obj = ma.ctx.GetClassObject(base_var->value.ToUint64());
  if (!obj) return false;
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ma.ctx.GetVariableClassType(ma.base_name);
  if (!declared.empty()) declared_type = ma.ctx.FindClassType(declared);
  out = ResolveClassFieldChain(obj, declared_type, ma.field_name, ma.ctx,
                               ma.arena);
  return true;
}

static bool TryClassEnumAccess(Variable* base_var, std::string_view field_name,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!base_var) return false;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return false;
  auto it = obj->type->enum_members.find(std::string(field_name));
  if (it == obj->type->enum_members.end()) return false;
  out = MakeLogic4VecVal(arena, 32, it->second);
  return true;
}

// Looks up a static property or enum member named `field_name` directly on
// `cls_type` (no inheritance walk). Returns true and fills `out` on a hit.
static bool TryLocalStaticMember(const ClassTypeInfo* cls_type,
                                 std::string_view field_name, Arena& arena,
                                 Logic4Vec& out) {
  auto it = cls_type->static_properties.find(std::string(field_name));
  if (it != cls_type->static_properties.end()) {
    out = it->second;
    return true;
  }
  auto eit = cls_type->enum_members.find(std::string(field_name));
  if (eit != cls_type->enum_members.end()) {
    out = MakeLogic4VecVal(arena, 32, eit->second);
    return true;
  }
  return false;
}

// Walks the interface-class inheritance graph rooted at `cls_type` (parent
// interface plus all extended interfaces) searching for a static property or
// enum member named `field_name`. Returns true and fills `out` on a hit.
static bool TryInterfaceStaticMember(const ClassTypeInfo* cls_type,
                                     std::string_view field_name, Arena& arena,
                                     Logic4Vec& out) {
  std::vector<const ClassTypeInfo*> stack;
  if (cls_type->parent && cls_type->parent->is_interface)
    stack.push_back(cls_type->parent);
  for (const auto* ei : cls_type->extended_interfaces) stack.push_back(ei);
  while (!stack.empty()) {
    const auto* cur = stack.back();
    stack.pop_back();
    if (TryLocalStaticMember(cur, field_name, arena, out)) return true;
    if (cur->parent && cur->parent->is_interface) stack.push_back(cur->parent);
    for (const auto* ei : cur->extended_interfaces) stack.push_back(ei);
  }
  return false;
}

// §8.13 (printed pages 189-190) with §8.9 (printed 186): `D::n` reads the
// static property D declares or inherits, the nearest declaration first, so
// where D extends C it reads C's one storage, what `C::n = 5` wrote. Read
// from D's own static_properties alone, which hold D's declarations, it
// answered 0.
static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  for (const auto* t = cls_type; t != nullptr; t = t->parent) {
    if (TryLocalStaticMember(t, field_name, arena, out)) return true;
  }
  return cls_type->is_interface &&
         TryInterfaceStaticMember(cls_type, field_name, arena, out);
}

// Resolves member access on the implicit `this`/`super` object. `is_super`
// selects the parent-type property view used by super. Returns true and fills
// `out` when `base_name` named one of those keywords.
static bool TryThisSuperMember(std::string_view base_name,
                               std::string_view field_name, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    // §8.11 with §7.2: `this.s.a` is a member of the structure the property s
    // holds, a path the property name alone does not answer; it is resolved
    // as a handle's `h.s.a` is, from the running method's class.
    out = self ? ResolveClassFieldChain(self, ctx.CurrentMethodClass(),
                                        field_name, ctx, arena)
               : MakeLogic4Vec(arena, 1);
    return true;
  }
  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    // §8.15: super resolves against the parent of the lexically enclosing class
    // (tracked during method execution); fall back to the dynamic type's parent
    // when no enclosing-class context is active.
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    const ClassTypeInfo* super_type =
        enclosing ? enclosing->parent
                  : (self && self->type ? self->type->parent : nullptr);
    if (self && super_type) {
      out = self->GetPropertyForType(field_name, super_type, arena);
    } else {
      out = MakeLogic4Vec(arena, 1);
    }
    return true;
  }
  return false;
}

// §11.9 (printed page 304): a member read inconsistent with the tagged
// union's current tag is a run-time error, and §7.3.2 (printed 151) makes
// that so for a tagged union wherever it stands -- the variable `u.Other`
// reads or the member `s.u.Other` reads, whose tag `s.u = tagged Valid 9`
// set under the member's own key. The walk FindUnionTagMismatch shares with
// the write side asks each tagged union on the path; this checked the base
// variable's own layout alone, a structure, and so read `s.u.Other` against
// no tag. Reports the error and fills `out` with all-X; true when it fired.
static bool TryUnionTagMismatch(const MemberAccess& ma,
                                const StructTypeInfo* sinfo, Logic4Vec& out) {
  UnionTagMismatch m =
      FindUnionTagMismatch(ma.base_name, sinfo, ma.field_name, ma.ctx);
  if (!m.found) return false;
  ma.ctx.GetDiag().Error(ma.loc,
                         "run-time error: accessing member '" + m.member +
                             "' of tagged union '" + m.union_name +
                             "' which currently has tag '" + m.tag + "'",
                         Subclause("11.9"));
  out = MakeAllX(ma.arena, sinfo->total_width);
  return true;
}

// §11.9 with §8.5: the same run-time error for a class property of a tagged
// union type, `o.None` in a method or `b.o.None` through a handle, read against
// the tag the property's own object holds (PropertyAggregateLayout). Reports
// the error and fills `out` with all-X; true when it fired.
static bool TryPropertyTagMismatch(const MemberAccess& ma, Logic4Vec& out) {
  std::string name(ma.base_name);
  std::string_view member = ma.field_name;
  if (ma.base_var != nullptr) {
    size_t dot = member.find('.');
    if (dot == std::string_view::npos) return false;
    name += '.';
    name += member.substr(0, dot);
    member = member.substr(dot + 1);
  }
  std::string key;
  const StructTypeInfo* layout = PropertyAggregateLayout(name, ma.ctx, key);
  if (layout == nullptr || !layout->is_union) return false;
  std::string_view tag = ma.ctx.GetVariableTag(key);
  if (tag.empty() || tag == member.substr(0, member.find('.'))) return false;
  ma.ctx.GetDiag().Error(ma.loc,
                         "run-time error: accessing member '" +
                             std::string(member) + "' of tagged union '" +
                             name + "' which currently has tag '" +
                             std::string(tag) + "'",
                         Subclause("11.9"));
  out = MakeAllX(ma.arena, layout->total_width);
  return true;
}

// Handles the named-event `.triggered` and named-sequence `.triggered`/`.ended`
// §16.13.5: whether the end point named `ep_name` is matched as read now,
// its match stored until the first tick of the reading clock after it.
static bool SequenceMatched(std::string_view ep_name, SimContext& ctx) {
  auto* ep = ctx.FindVariable(ep_name);
  if (ep == nullptr) return false;
  return ctx.ConsumeSequenceMatch(ep_name, ep->triggered_ticks,
                                  ctx.CurrentTime().ticks);
}

// §16.9.11 and §16.13.5: `triggered` and `matched` on the end point
// `ep_name`, the first true at the time step of the match alone and the
// second storing a match until the first tick of the reading clock after
// it; false where `field_name` names neither.
static bool TryEndPointMethod(std::string_view ep_name,
                              std::string_view field_name, SimContext& ctx,
                              Arena& arena, Logic4Vec& out) {
  if (field_name != "triggered" && field_name != "matched") return false;
  bool reached = field_name == "matched" ? SequenceMatched(ep_name, ctx)
                                         : ctx.IsEventTriggered(ep_name);
  out = MakeLogic4VecVal(arena, 1, reached ? 1u : 0u);
  return true;
}

// The same on the named sequence `base_name`, whose end point the instance
// reading it declares.
static bool TrySequenceEndPointMethod(std::string_view base_name,
                                      std::string_view field_name,
                                      SimContext& ctx, Arena& arena,
                                      Logic4Vec& out) {
  return TryEndPointMethod("__seq_" + std::string(base_name), field_name, ctx,
                           arena, out);
}

// §16.13.6 with §23.6: `triggered` or `matched` applied to a sequence named
// through the instance hierarchy, `u.s.triggered`, reads the end point of the
// sequence s declared in the instance u, which s's monitor in u fires under
// u's prefix; false where the name selects no instance's sequence.
static bool TryHierarchicalSequenceMethod(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      expr->lhs->kind != ExprKind::kMemberAccess) {
    return false;
  }
  std::string ep_name =
      HierarchicalEndPoint(HierarchicalReferenceName(expr->lhs), ctx);
  if (ep_name.empty()) return false;
  return TryEndPointMethod(ep_name, expr->rhs->text, ctx, arena, out);
}

// pseudo-methods. Returns true and fills `out` when `field_name` named one of
// these and the base referred to a matching event/sequence.
static bool TryEventSequenceMethod(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  SimContext& ctx = ma.ctx;
  Arena& arena = ma.arena;
  std::string_view base_name = ma.base_name;
  std::string_view field_name = ma.field_name;
  if (base_var && base_var->is_event && field_name == "triggered") {
    // §15.5.3: the triggered method of a null named event evaluates to false,
    // independent of any triggered state recorded for the current time step.
    out = base_var->is_null_event
              ? MakeLogic4VecVal(arena, 1, 0u)
              : MakeLogic4VecVal(arena, 1,
                                 ctx.IsEventTriggered(base_name) ? 1u : 0u);
    return true;
  }
  if (!base_var && ctx.FindSequenceDecl(base_name) &&
      TrySequenceEndPointMethod(base_name, field_name, ctx, arena, out)) {
    return true;
  }
  if (!base_var && field_name == "ended" && ctx.FindSequenceDecl(base_name)) {
    // Annex C.2.3: IEEE 1800-2005 supplied the ended sequence method to detect
    // a sequence end point inside a sequence expression, while triggered served
    // the same role in other contexts. The two had identical meaning but
    // mutually exclusive uses, so this version retires ended and lets triggered
    // cover both. A reference to ended on a named sequence therefore names a
    // removed method and is reported rather than silently evaluated.
    ctx.GetDiag().Error(
        ma.loc,
        "the ended sequence method has been removed; use the triggered "
        "method to detect the end point of sequence '" +
            std::string(base_name) + "'",
        Subclause("C.2.3"));
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  return false;
}

// §15.5.3: `function bit triggered()` may be called with its empty argument
// list, `ev.triggered()`, as well as without, the member form
// TryEventSequenceMethod serves; this is the call form, on a named event --
// a package's `p::e.triggered()` by its "p.e" key -- or on a class's event
// property (TryClassEventTriggered), 0 for a null event.
bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  if (parts.method_name != "triggered") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var || !var->is_event)
    return TryClassEventTriggered(expr, ctx, arena, out);
  out = var->is_null_event
            ? MakeLogic4VecVal(arena, 1, 0u)
            : MakeLogic4VecVal(arena, 1,
                               ctx.IsEventTriggered(parts.var_name) ? 1u : 0u);
  return true;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena,
                                     SourceLoc loc) {
  Logic4Vec out;
  if (TryThisSuperMember(base_name, field_name, ctx, arena, out)) return out;

  auto* base_var = ctx.FindVariable(base_name);
  // §23.9: the base resolves within the running instance, so its layout is
  // asked for by the key that instance's storage was created under.
  const StructTypeInfo* sinfo = StructLayoutOfName(base_name, ctx);

  MemberAccess ma{base_name, field_name, base_var, ctx, arena, loc};

  if (base_var && sinfo) {
    if (TryUnionTagMismatch(ma, sinfo, out)) {
      return out;
    }
    return ExtractStructField(base_var, sinfo, field_name, arena);
  }
  if (TryPropertyTagMismatch(ma, out)) return out;

  if (TryEventSequenceMethod(ma, out)) {
    return out;
  }

  // §8.26: a class-scoped enum literal accessed through an instance handle
  // (p.ERR_OVERFLOW) resolves to its enum value. This is tried before the
  // general property read, which would otherwise claim the (unknown) name and
  // return 0; a name that is not an enum member falls through to it.
  if (TryClassEnumAccess(base_var, field_name, ctx, arena, out)) return out;
  if (TryClassPropertyAccess(ma, out)) return out;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryClockvarMemberAccess(base_name, field_name, ctx, arena, out))
    return out;
  if (TryImplicitThisHandleMember(base_name, field_name, ctx, arena, out))
    return out;
  return MakeLogic4Vec(arena, 1);
}

// §16.5.2: "In an assertion, the sampled value is the only valid value of a
// variable during a clock tick", and §16.5.1 puts no condition on where the
// variable is declared, so a variable a property reaches across an instance
// boundary reads the value sampled for this time slot exactly as one the
// module declares itself. The store answers nothing outside a clocked
// concurrent assertion's property and nothing for a variable no such property
// reads, so every other hierarchical read is the live read it was.
static Logic4Vec ReadReferencedVariable(const Variable& var, SimContext& ctx) {
  const Logic4Vec* sampled =
      ctx.AssertionSamples().ReadWithinProperty(&var, ctx.CurrentTime());
  Logic4Vec val = sampled != nullptr ? *sampled : var.value;
  // §11.8.1: the operand's signedness is its declaration's, whatever the value
  // stored in it carried, as EvalIdentifier derives it for a simple name:
  // `logic w` set to the signed literal 1 and read as `a.w` read -1.
  val.is_signed = var.is_signed;
  return val;
}

// §25.9: a component referenced through a virtual interface redirects to the
// bound interface instance. Referencing a component of an unbound (null or
// uninitialized) virtual interface is a fatal runtime error. Returns true and
// fills `out` when `expr` accessed a member through a virtual interface: a
// variable declared so, a property declared so of the class whose method is
// running, or, `this.vif.a` and `d.vif.a`, a property declared so of the
// object a handle expression denotes, which ResolveVirtualInterfaceBaseExpr
// tells apart from any other base. Before the base was resolved as an
// expression, `d.vif.a` fell to the class field chain, which took the
// interface handle for a class handle, found no object, and read a flattened
// key the class never declared.
static bool TryVirtualInterfaceMember(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(expr->lhs, ctx, arena);
  // §27.5 with §23.6: `vif.g.v`, through a named generate block of it.
  std::string inner;
  if (!base.is_virtual_interface) {
    base = ResolveVirtualInterfaceInnerPath(expr, ctx, arena, inner);
  }
  if (!base.is_virtual_interface) return false;
  if (base.handle == kNullVirtualInterface) {
    ctx.GetDiag().Error(expr->range.start,
                        "reference through a null virtual interface",
                        Subclause("25.9"));
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  std::string_view field =
      (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
          ? expr->rhs->text
          : std::string_view(expr->text);
  if (!inner.empty()) field = inner;
  auto* tv =
      ctx.FindVariable(VirtualInterfaceComponentName(base.handle, field, ctx));
  // §16.5.1 with §25.9: sampled within a property, and signed as declared.
  out = tv ? ReadReferencedVariable(*tv, ctx) : MakeLogic4Vec(arena, 1);
  return true;
}

// §8.25.1: an explicit specialization used as the scope-resolution prefix
// (`C#(3)::p`) denotes the parameter in that specialization, not the class's
// default. When the accessed name is a value parameter port that the prefix
// overrides -- by ordered position or by name -- evaluate the override
// expression instead of falling through to the default stored on the class.
// Type parameters carry no value and body-local parameters are not overridable
// through `#(...)`, so both are left to the ordinary member-access path.
// §8.25.1: the port position `name` occupies in a class's parameter port list.
// A type parameter carries no value and is not overridable through #(...), so
// it has no position here.
static size_t ValueParamPosition(const ClassDecl& decl, std::string_view name) {
  if (decl.type_param_names.count(name)) return decl.params.size();
  for (size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first == name) return i;
  }
  return decl.params.size();
}

// §8.25.1: the specialization argument that overrides `name`. A named override
// binding the parameter takes precedence regardless of its position in the
// override list; otherwise the ordered override occupying the parameter's own
// port position applies.
static const Expr* FindSpecializationOverride(const Expr& base,
                                              const ClassDecl& decl,
                                              std::string_view name) {
  size_t pos = ValueParamPosition(decl, name);
  if (pos == decl.params.size()) return nullptr;
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == name && elems[j])
      return elems[j];
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size()) return elems[pos];
  return nullptr;
}

static bool TryParameterizedScopeParam(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier ||
      !expr->lhs->has_param_spec || expr->lhs->elements.empty())
    return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls || !cls->decl) return false;
  const Expr* override_expr =
      FindSpecializationOverride(*expr->lhs, *cls->decl, expr->rhs->text);
  if (override_expr == nullptr) return false;
  out = EvalExpr(override_expr, ctx, arena);
  return true;
}

// §16.9.11, §16.13.5 and §16.13.6: whether the expression applies
// `triggered` or `matched` to a sequence instance with arguments, `e2(ready,
// proc1, proc2).triggered`, to a sequence actual, the identifier carrying it
// standing where the formal of `subseq.triggered` stood, or to a name the
// lowering gave an end point of its own for the clock of its context.
static bool ReadsAMonitorEndPoint(const Expr* expr, SimContext& ctx) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      (expr->rhs->text != "triggered" && expr->rhs->text != "matched")) {
    return false;
  }
  if (expr->lhs->kind == ExprKind::kCall) {
    return ctx.FindSequenceDecl(expr->lhs->callee) != nullptr;
  }
  return expr->lhs->kind == ExprKind::kIdentifier &&
         (expr->lhs->property_actual != nullptr ||
          !ctx.FindSequenceInstanceEndpoint(expr->lhs).empty());
}

// §16.9.11, §16.13.5 and §16.13.6: `.triggered` or `.matched` applied to a
// sequence instance with arguments or to a sequence actual reads the
// endpoint of the monitor the lowering gave it; answers false where no
// monitor was made for it.
static bool TryInstanceTriggered(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (!ReadsAMonitorEndPoint(expr, ctx)) return false;
  std::string_view ep_name = ctx.FindSequenceInstanceEndpoint(expr->lhs);
  bool triggered = !ep_name.empty() && (expr->rhs->text == "matched"
                                            ? SequenceMatched(ep_name, ctx)
                                            : ctx.IsEventTriggered(ep_name));
  out = MakeLogic4VecVal(arena, 1, triggered ? 1u : 0u);
  return true;
}

// The member selects that are no read of a member of a value: a sequence's
// end point (§16.9.11), an array reduction or ordering method with a with
// clause (§7.12), a parameter of a parameterized class scope (§8.25.1), and a
// process (§9.7), enumeration (§6.19.5.7) or semaphore (§15.3) method written
// without an argument list, `p.kill`, `c.next` or `s.try_get`, which leave no
// member of the name to read. True with `out` set when the select was one.
static bool TryMemberSelectThatIsNoRead(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out) {
  if (TryInstanceTriggered(expr, ctx, arena, out)) return true;
  if (TryHierarchicalSequenceMethod(expr, ctx, arena, out)) return true;
  if (TryEvalArrayReductionWithClause(expr, ctx, arena, out)) return true;
  // §7.12.2: a bare-member sort()/rsort() carrying a with clause (parenthesis-
  // free form, or any queue receiver) reorders in place; yield a void result.
  if (TryExecArrayOrderingWithClauseStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return TryParameterizedScopeParam(expr, ctx, arena, out) ||
         TryScopeSpecializationStaticMember(expr, ctx, arena, out) ||
         TryEvalProcessMethodWithoutArgs(expr, ctx, arena, out) ||
         TryEvalEnumMethodWithoutArgs(expr, ctx, arena, out) ||
         TryEvalSemaphoreMethodCall(expr, ctx, arena, out) ||
         TryClassEventTriggered(expr, ctx, arena, out);
}

// §7.8.7: `b[2].x` reads a member of an associative array element, and §8.4
// `q[1].v` or `a[1].v` a property of the object an element of a queue or of
// an array property (§7.4.2) refers to; the name EvalMemberAccess builds
// reaches none. §8.6: nor `n.self().v`, a property of the object a method call
// returned. §8.9 with §8.4: nor `C::m_inst.k` or a static method's bare
// `m_inst.k`, a property of the object a static property holds a handle to.
static bool TryObjectMemberRead(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  return TryEvalAssocMemberField(expr, ctx, arena, out) ||
         TryEvalElementObjectMember(expr, ctx, arena, out) ||
         TryEvalCallResultMember(expr, ctx, arena, out) ||
         TryPackageClassStaticMember(expr, ctx, arena, out) ||
         TryStaticHandleMember(expr, ctx, arena, out);
}

// §18.7.1: a name qualified by local:: — the local::x used to steer an inline
// randomize()...with constraint from the calling scope — bypasses the
// randomized object's class scope and resolves in the scope containing the
// method call, which is exactly the scope this expression is evaluated in.
// `local` is a reserved keyword and cannot name any declaration, so a leading
// "local." segment can only be that qualifier: it is dropped from `resolved`,
// so local::x denotes the same declaration an unqualified x written in this
// scope would. local::this binds to the scope containing the call, whose
// `this` the constraint evaluation keeps aside while the randomized object
// stands in scope as `this`; true with `out` read through it.
static bool TryLocalScopeQualifier(std::string& resolved, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  constexpr std::string_view kLocalScopePrefix = "local.";
  if (!std::string_view(resolved).starts_with(kLocalScopePrefix)) return false;
  resolved = resolved.substr(kLocalScopePrefix.size());
  constexpr std::string_view kThisPrefix = "this.";
  ClassObject* caller = ctx.ConstraintCallerThis();
  if (caller == nullptr ||
      !std::string_view(resolved).starts_with(kThisPrefix)) {
    return false;
  }
  out = ResolveClassFieldChain(caller, nullptr,
                               resolved.substr(kThisPrefix.size()), ctx, arena);
  return true;
}

// Whether the path `expr` starts at no variable or array, so a select after it
// picks an instance, not an element, whose index would then be read twice.
static bool HeadNamesAnInstance(const Expr* expr, SimContext& ctx) {
  const Expr* head = expr;
  while (head->kind == ExprKind::kMemberAccess ||
         head->kind == ExprKind::kSelect) {
    head = head->kind == ExprKind::kSelect ? head->base : head->lhs;
    if (head == nullptr) return false;
  }
  return head->kind == ExprKind::kIdentifier &&
         ctx.FindVariable(head->text) == nullptr &&
         ctx.FindArrayInfo(head->text) == nullptr;
}

// The variable the path `expr`, spelled `resolved`, names: `$root`-headed from
// the top first (§23.3.1), a non-literal instance select by its value (§23.6).
static Variable* FindReferencedVariable(const Expr* expr,
                                        const std::string& resolved,
                                        SimContext& ctx, Arena& arena) {
  std::string rooted = RootedReferenceKey(expr);
  auto* var = rooted.empty() ? nullptr : ctx.FindVariable(rooted);
  if (var == nullptr) var = ctx.FindVariable(resolved);
  if (var == nullptr && HeadNamesAnInstance(expr, ctx)) {
    var = ctx.FindVariable(EvaluatedHierarchicalPath(expr, ctx, arena));
  }
  return var;
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (TryContainerElementMember(expr, ctx, arena, out)) return out;
  if (TryEvalStringMethodWithoutParens(expr, ctx, arena, out)) return out;
  if (TryMemberSelectThatIsNoRead(expr, ctx, arena, out)) return out;

  if (TryClockvarPathRead(expr, ctx, arena, out)) return out;
  if (TryVirtualInterfaceMember(expr, ctx, arena, out)) return out;

  if (TryObjectMemberRead(expr, ctx, arena, out)) return out;
  if (TryEvalCovergroupOptionRead(expr, ctx, arena, out)) return out;

  auto resolved = HierarchicalReferenceName(expr);
  if (TryLocalScopeQualifier(resolved, ctx, arena, out)) return out;
  if (auto* var = FindReferencedVariable(expr, resolved, ctx, arena)) {
    return ReadReferencedVariable(*var, ctx);
  }

  auto dot = MemberPathSplit(resolved, ctx);
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(resolved).substr(0, dot);
  // §23.7: a name whose head is no variable may be `f.x`, the static local
  // of the function f.
  if (ctx.FindVariable(base_name) == nullptr) {
    if (Variable* local = FunctionStaticLocal(expr, ctx, arena)) {
      return local->value;
    }
  }
  auto field_name = std::string_view(resolved).substr(dot + 1);
  return ResolveMemberByType(base_name, field_name, ctx, arena,
                             expr->range.start);
}

}  // namespace delta
