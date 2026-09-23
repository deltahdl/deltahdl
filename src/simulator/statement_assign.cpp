#include "simulator/statement_assign.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

// §7.3.2 (printed page 151) has a tagged union carry its tag wherever it
// stands, a variable or a member of one, and a member's tag stands under the
// variable's key followed by the member path (EvalRhsForTaggedMember), "s.u"
// for `s.u = tagged Valid 9`. The walk a dotted member path takes down from a
// variable's layout, one segment at a time: the tag key and the spelling of
// the object the walk stands at, kept beside that object's layout and the
// segments still to descend.
struct MemberPathCursor {
  std::string key;
  std::string name;
  std::string_view path;
  const StructTypeInfo* layout = nullptr;
};

// The walk at `base_name` itself, its tag asked for by the key the variable's
// storage was created under (§23.9, TagKeyOfName), as its layout is; by the
// bare name, a union initialized in its declaration inside a child instance
// was checked against no tag.
static MemberPathCursor BeginMemberPath(std::string_view base_name,
                                        const StructTypeInfo* info,
                                        std::string_view field_name,
                                        SimContext& ctx) {
  return {TagKeyOfName(base_name, ctx), std::string(base_name), field_name,
          info};
}

// Enters the member the path's next segment names. False, the cursor left as
// it was, where the path is spent or the layout declares no such member.
static bool DescendMemberPath(MemberPathCursor& c) {
  if (c.path.empty() || c.layout == nullptr) return false;
  size_t dot = c.path.find('.');
  std::string_view seg = c.path.substr(0, dot);
  const StructFieldInfo* field = FindStructField(c.layout, seg);
  if (field == nullptr) return false;
  c.key += '.';
  c.key += seg;
  c.name += '.';
  c.name += seg;
  c.path = dot == std::string_view::npos ? std::string_view{}
                                         : c.path.substr(dot + 1);
  c.layout = field->nested;
  return true;
}

UnionTagMismatch FindUnionTagMismatch(std::string_view base_name,
                                      const StructTypeInfo* info,
                                      std::string_view field_name,
                                      SimContext& ctx) {
  MemberPathCursor c = BeginMemberPath(base_name, info, field_name, ctx);
  UnionTagMismatch found;
  while (c.layout != nullptr && !c.path.empty()) {
    if (c.layout->is_union) {
      std::string_view tag = ctx.GetVariableTag(c.key);
      if (!tag.empty() && tag != c.path.substr(0, c.path.find('.'))) {
        found.union_name = c.name;
        found.member = std::string(c.path);
        found.tag = std::string(tag);
        found.found = true;
        return found;
      }
    }
    if (!DescendMemberPath(c)) break;
  }
  return found;
}

MemberLayout ResolveMemberLayout(std::string_view base_name,
                                 const StructTypeInfo* info,
                                 std::string_view field_name, SimContext& ctx) {
  MemberPathCursor c = BeginMemberPath(base_name, info, field_name, ctx);
  while (!c.path.empty()) {
    if (!DescendMemberPath(c)) return {};
  }
  MemberLayout member;
  member.layout = c.layout;
  if (c.layout != nullptr && c.layout->is_union) {
    member.tag = std::string(ctx.GetVariableTag(c.key));
  }
  return member;
}

// §11.9 (printed page 304): a value assigned to a member of a tagged union
// shall be consistent with the union's current tag, a run-time error
// otherwise, and §7.3.2 (printed 151) makes that so for a tagged union
// wherever it stands -- a variable, `u.Other = 3`, or a member of one,
// `s.u.Other = 3`. Returns true, with the error emitted, when a write targets
// a member inconsistent with a tag on the way (FindUnionTagMismatch); the
// caller treats that as a handled no-op write. `loc` is where the target was
// written: the names arrive as text rebuilt from the target expression,
// which carries the position they lost.
static bool TaggedUnionTagMismatch(std::string_view base_name,
                                   const StructTypeInfo* info,
                                   std::string_view field_name, SimContext& ctx,
                                   SourceLoc loc) {
  UnionTagMismatch m = FindUnionTagMismatch(base_name, info, field_name, ctx);
  if (!m.found) return false;
  ctx.GetDiag().Error(loc,
                      "run-time error: assigning member '" + m.member +
                          "' of tagged union '" + m.union_name +
                          "' which currently has tag '" + m.tag + "'",
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
  window.total_width = info->total_width;
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
static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name);

static FieldTarget ResolveClassFieldTarget(ClassObject* obj,
                                           const ClassTypeInfo* declared_type,
                                           std::string_view field_path,
                                           SimContext& ctx) {
  auto dot = field_path.find('.');
  if (dot != std::string_view::npos) {
    auto& arena = ctx.GetArena();
    auto first = field_path.substr(0, dot);
    // §7.2.1: `first` declared with a structure's type holds that structure
    // rather than a handle, so the rest of the path selects a member of it.
    // Asked before the handle lookup, because a structure whose bits happen to
    // equal a live handle's number is still a structure. The flattened key
    // below would store the value under a name the class never declared and
    // leave the property the path actually names untouched.
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
      bits.holder_width = window.total_width;
      return bits;
    }
    Logic4Vec handle_val =
        declared_type ? obj->GetPropertyForType(first, declared_type, arena)
                      : obj->GetProperty(first, arena);
    if (auto* next_obj = ctx.GetClassObject(handle_val.ToUint64())) {
      return ResolveClassFieldTarget(next_obj, nullptr,
                                     field_path.substr(dot + 1), ctx);
    }
  }
  // §8.9 (printed page 186): a static property named through a handle,
  // `m_t_inst.m_tw_cb_q`, is the class's one storage, so the deposit goes
  // where `C::m_tw_cb_q = v` goes (StaticPropertyTarget), as the read side
  // already reads it; deposited in the object's own map, the class's copy
  // stayed null for every read of it.
  const ClassTypeInfo* scope = declared_type ? declared_type : obj->type;
  if (scope != nullptr && scope->StaticPropertyDeclarer(field_path) != nullptr)
    return StaticPropertyTarget(scope, field_path);
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

// §8.11 with §8.15: the property `field_name` of the object the running
// method runs on, as the method's class declares it -- what a bare name in
// the same method names -- else null where no method is running. The
// declaring type scopes the deposit: a property is kept under a `Type::name`
// key beside its bare key, and every read inside a method consults the
// scoped key first, so a deposit under the bare key alone -- what a `this.x`
// nonblocking assignment made -- sat unseen beside the stale scoped value.
static FieldTarget ResolveOwnPropertyTarget(std::string_view field_name,
                                            SimContext& ctx) {
  auto* self = ctx.CurrentThis();
  if (!self) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = self;
  target.type = ctx.CurrentMethodClass();
  target.field = std::string(field_name);
  return target;
}

// §8.11 with §7.2: `p.f` written inside a method, where `p` names no variable
// but a property of the running method's object. The member path is resolved
// against that object exactly as `h.p.f` is against the object `h` names, so
// the window of the structure `p` holds is what takes the value; a `p` that
// holds a handle is followed into its object the same way. *handled is set
// true when the name is such a property; a local of the name is its own
// declaration and shadows the property (§8.11), so it is left to
// ResolveVariableField, while a variable of the module enclosing the class
// does not shadow it (§23.9), which NameDenotesVariable tells apart as
// TryFuncClassTargetWrite does for the bare name.
static FieldTarget ResolveOwnPropertyMemberTarget(std::string_view base_name,
                                                  std::string_view field_name,
                                                  SimContext& ctx,
                                                  bool* handled) {
  *handled = false;
  auto* self = ctx.CurrentThis();
  if (self == nullptr || NameDenotesVariable(base_name, ctx)) return {};
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  const ClassTypeInfo* start = enclosing != nullptr ? enclosing : self->type;
  if (FindPropertyInfo(start, base_name) == nullptr) return {};
  *handled = true;
  std::string path = std::string(base_name) + "." + std::string(field_name);
  return ResolveClassFieldTarget(self, enclosing, path, ctx);
}

static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name);

FieldTarget ResolveBarePropertyTarget(std::string_view name, SimContext& ctx) {
  auto* self = ctx.CurrentThis();
  if (self != nullptr && self->type != nullptr &&
      self->type->FindProperty(name) != nullptr) {
    return ResolveOwnPropertyTarget(name, ctx);
  }
  // §8.10 with §8.9: a static method runs on no object, and a static property
  // it names bare is the class's one copy, the declaring class's storage as
  // `C::name` reaches it (StaticPropertyTarget); §8.23 lets a nested class's
  // method name a containing class's static property the same way, which is
  // the chain StaticPropertyOwner walks. Answered on no object at all, the
  // bare name in a static method named no storage.
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassTypeInfo* owner =
      method_cls != nullptr ? method_cls->StaticPropertyOwner(name) : nullptr;
  return owner != nullptr ? StaticPropertyTarget(owner, name) : FieldTarget{};
}

// The field of the current `this` object. *handled is set true when base_name
// names `this`; the target answered is then the whole answer.
static FieldTarget ResolveThisField(std::string_view base_name,
                                    std::string_view field_name,
                                    SimContext& ctx, bool* handled) {
  *handled = false;
  if (base_name != "this") return {};
  *handled = true;
  return ResolveOwnPropertyTarget(field_name, ctx);
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

// §8.13 (printed pages 189-190) with §8.9 (printed 186): the static property
// `field_name` of `cls` or of a base it inherits it from, as the storage of
// the class declaring it -- C's for `D::n = 2` where D extends C, which is
// what `C::n` reads and the class the deposit notifies, the one every wait
// on the property is armed on (ClassTypeInfo::StaticPropertyDeclarer). No
// target where no class on the chain declares it. Asked of D's own
// static_properties, which hold D's declarations alone, the write found no
// slot and landed nowhere.
static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name) {
  const ClassTypeInfo* declarer = cls->StaticPropertyDeclarer(field_name);
  if (declarer == nullptr) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kStatic;
  target.type = declarer;
  target.slot =
      &declarer->static_properties.find(std::string(field_name))->second;
  target.field = std::string(field_name);
  return target;
}

// §8.25 (printed page 204 of IEEE 1800-2023): `S#(byte)::n = 5` writes the
// static property of the specialization the scope form names, each
// specialization holding its own set of static member variables, as the read
// of `S#(byte)::n` does (TryScopeSpecializationStaticMember). The flattened
// name drops the parameter list, so ResolveStaticClassField took `S` for the
// class and the value landed in the default specialization's n. *handled is
// set true where the left side of the scope form names a specialization.
static FieldTarget ResolveSpecializationStaticField(const Expr* lhs,
                                                    SimContext& ctx,
                                                    bool* handled) {
  *handled = false;
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const ClassTypeInfo* spec =
      ScopeNamedSpecialization(lhs->lhs, ctx, ctx.GetArena());
  if (spec == nullptr) return {};
  *handled = true;
  return StaticPropertyTarget(spec, lhs->rhs->text);
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
  return StaticPropertyTarget(cls_type, field_name);
}

// §8.9 (printed page 186) with §8.4 (printed 181-182): `C::m_inst.k = v`,
// `p::C::m_inst.k = v` and the bare `m_inst.k = v` of a static method
// (§8.10, printed 186) write the property of the object the static property
// holds a handle to, resolved on that object as `h.k = v` is on the
// variable's (ResolveClassFieldTarget, the declared class scoping the
// deposit as §8.15 asks). The flattened name parted at "C.m_inst", which
// names no variable, and the bare base met no `this`, so each write went
// nowhere while the object's k kept its 9. *handled is set true where the
// base names a static property holding a live object; a null one is left to
// the resolvers below, which answer no storage for it as they do for a null
// variable.
static FieldTarget ResolveStaticHandleField(const Expr* lhs, SimContext& ctx,
                                            bool* handled) {
  *handled = false;
  StaticPropertyRef ref;
  std::string path;
  if (!ResolveStaticHandlePath(lhs, ctx, ctx.GetArena(), ref, path)) return {};
  std::string_view declared_key;
  ClassObject* obj = StaticPropertyObject(ref, ctx, &declared_key);
  if (obj == nullptr) return {};
  *handled = true;
  return ResolveClassFieldTarget(obj, ctx.FindClassType(declared_key), path,
                                 ctx);
}

// §8.9 with §26.3: the static property `pk::Cfg::x` names of the package's
// class. The flattened name below would take `pk` for the class, which it is
// not, so the expression is asked before it is flattened. *handled is set
// true when the expression names a package's class.
static FieldTarget ResolvePackageClassStaticField(const Expr* lhs,
                                                  SimContext& ctx,
                                                  bool* handled) {
  *handled = false;
  std::string_view member;
  const ClassTypeInfo* cls = PackageQualifiedClassOf(lhs, ctx, member);
  if (cls == nullptr) return {};
  *handled = true;
  return StaticPropertyTarget(cls, member);
}

// The component the member access `lhs` names of the interface instance its
// base is bound to. §25.9 has every component of the instance a virtual
// interface represents reachable through it by the dot notation once it is
// initialized, in procedural statements alone, and an assignment is such a
// statement -- the clause's own example writes `bus.req <= 1'b1`. The
// component belongs to the instance, so the path names that instance's own
// variable and the write lands there.
//
// One arm serves both assignment forms, because both reach here: the blocking
// one through WriteStructField, which resolves and deposits at the one moment,
// and the nonblocking one through ScheduleFieldNba, which asks this alone when
// the statement executes and defers only the deposit. That is also where
// §10.4.2 wants a virtual interface reference in an lvalue evaluated, at the
// same time as the right-hand side, so the binding read here is the one in
// force when the statement ran, not the one in the update region.
//
// *handled is set true when the base names a virtual interface, bound or
// not: a variable declared so, a property declared so of the class whose
// method is running, which is how the clause's transactor writes `bus.req`,
// or a property declared so of the object a handle expression denotes,
// `this.vif.a <= 1` in a method and `d.vif.a <= 1` from the module or
// another object (ResolveVirtualInterfaceBaseExpr). An unbound one is the
// null reference §25.9 makes a runtime error -- the same one a read through
// it raises -- reported here and resolved to storage that takes no value, so
// the caller sees a handled path rather than an unwritten one it would report
// again or drop in silence.
static FieldTarget ResolveVirtualInterfaceField(const Expr* lhs,
                                                SimContext& ctx,
                                                bool* handled) {
  *handled = false;
  if (lhs->kind != ExprKind::kMemberAccess || lhs->is_scope_resolution ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(lhs->lhs, ctx, ctx.GetArena());
  if (!base.is_virtual_interface) return {};
  *handled = true;
  if (base.handle == kNullVirtualInterface) {
    ctx.GetDiag().Error(lhs->range.start,
                        "reference through a null virtual interface",
                        Subclause("25.9"));
    FieldTarget target;
    target.kind = FieldTarget::Kind::kNoOp;
    return target;
  }
  auto* component = ctx.FindVariable(
      VirtualInterfaceComponentName(base.handle, lhs->rhs->text, ctx));
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
  // §23.9: the base resolves within the running instance, so its layout is
  // asked for by the key that instance's storage was created under; asked by
  // the bare name, a member write inside a child instance found no layout and
  // went nowhere.
  const StructTypeInfo* info = StructLayoutOfName(base_name, ctx);
  if (info) {
    FieldTarget target;
    if (TaggedUnionTagMismatch(base_name, info, field_name, ctx, loc)) {
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

// §26.3 with §8.4: `p::h.v` writes a property of the object the package
// variable `p::h` holds. The flattened name "p.h.v" parts at its first dot,
// which takes the package for the variable; a member path rooted in a package
// scope resolution -- `p::h` at the left end of the chain, however many
// members follow it -- parts after the "p.h" the package's storage is keyed
// by instead. Answers the first dot for every other target.
static size_t FieldTargetSplit(const Expr* lhs, const std::string& name) {
  const Expr* root = lhs;
  while (root->kind == ExprKind::kMemberAccess && !root->is_scope_resolution &&
         root->lhs != nullptr) {
    root = root->lhs;
  }
  bool scoped_root = root != lhs && root->kind == ExprKind::kMemberAccess &&
                     root->is_scope_resolution && root->lhs != nullptr &&
                     root->lhs->kind == ExprKind::kIdentifier &&
                     root->rhs != nullptr &&
                     root->rhs->kind == ExprKind::kIdentifier;
  if (scoped_root) return root->lhs->text.size() + 1 + root->rhs->text.size();
  return name.find('.');
}

FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx) {
  // A virtual interface base is asked first, on the expression rather than
  // the flattened name: `this.vif.a` splits to `this` and `vif.a`, which
  // ResolveThisField would take for a property named by the flat key, and
  // `d.vif.a` to `d` and `vif.a`, which ResolveVariableField would follow
  // into the object `d` and take the interface handle for a class handle. A
  // bare `this`, `super` or class type name resolves to no virtual interface,
  // so those bases still reach their own resolvers below.
  bool handled = false;
  FieldTarget target = ResolveVirtualInterfaceField(lhs, ctx, &handled);
  if (handled) return target;
  target = ResolvePackageClassStaticField(lhs, ctx, &handled);
  if (handled) return target;
  target = ResolveStaticHandleField(lhs, ctx, &handled);
  if (handled) return target;
  target = ResolveSpecializationStaticField(lhs, ctx, &handled);
  if (handled) return target;

  std::string name;
  BuildLhsName(lhs, name);
  auto dot = FieldTargetSplit(lhs, name);
  if (dot == std::string::npos) return {};
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);

  target = ResolveThisField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveSuperField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveStaticClassField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveOwnPropertyMemberTarget(base_name, field_name, ctx, &handled);
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

// §7.2 with §6.8: the property holds the whole structure, so its value is as
// wide as the structure's layout before a member is deposited into it.
// CollectClassMembers sizes a property declared by a typedef name to a 32-bit
// carrier, into which a member above bit 31 cannot be deposited -- `pair_t p`
// with two int members lost `p.f`, the upper one, while `p.g` at the bottom
// landed. The bits the widening exposes are the zeros the carrier was filled
// with; the value is widened unsigned so no sign of the carrier's is extended
// over them.
static Logic4Vec WidenToHolder(Logic4Vec held, uint32_t holder_width,
                               Arena& arena) {
  if (held.width >= holder_width) return held;
  held.is_signed = false;
  return ResizeToWidth(held, holder_width, arena);
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
      Logic4Vec updated =
          WidenToHolder(OwnRhsWords(held, arena), target.holder_width, arena);
      DepositBitField(updated, target.bit_offset, rhs_val, target.width);
      SetClassField(target.obj, target.type, target.field, updated, arena);
      if (target.notify) target.notify->NotifyWatchers();
      if (target.obj) ctx.NotifyClassHandleWatchers(target.obj->handle);
      return;
    }
    case FieldTarget::Kind::kStatic:
      *target.slot =
          CoerceToPropertyType(target.type, target.field, rhs_val, arena);
      // §9.4.2 with §8.9: the storage is the class's own, which no object's
      // watchers see written, so the write is announced on the class, where
      // an event control or a wait on `C::n` armed -- the declaring class,
      // C for `D::n` (§8.13), the one storage both names reach.
      target.type->NotifyStaticWatchers();
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
