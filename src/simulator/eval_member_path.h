#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class Arena;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct Logic4Vec;
struct QueueObject;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;
struct Variable;

// §7.2 with §7.4.2: the element of an unpacked array member of a structure
// variable that a select names, `m.v[1]`: the variable holding the structure
// and the element's window of its bits. `in_range` is false for an index
// outside the member's bounds or holding x or z, which reads x and writes
// nothing.
struct StructArrayElementRef {
  // The value holding the structure: a variable's, or a class property's
  // (§8.5), which no variable stands for, `var` then null.
  Logic4Vec* value = nullptr;
  Variable* var = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  bool is_signed = false;
  bool in_range = false;
};

// Resolves `select` when it indexes an unpacked array member of a structure
// variable -- a module's, a block's or a subroutine's, bare or through a
// nested member, `m.v[1]` or `m.s.v[1]` -- or of a structure a class property
// holds, named bare in a method, through `this` or through a handle,
// `s.data[2]`, `this.s.data[2]`, `h.s.data[2]`. False for any other select,
// which the caller reads or writes as before.
bool ResolveStructArrayElement(const Expr* select, SimContext& ctx,
                               Arena& arena, StructArrayElementRef& out);

// §7.2 with §7.4.2: the unpacked array member a member access names, `m.v`,
// `r.v` bare in a method, `this.r.v` or `h.r.v`, as the structure's layout
// records it (its element count and bounds); null where the access names no
// such member.
const StructFieldInfo* ResolveStructArrayMember(const Expr* access,
                                                SimContext& ctx);

// §7.2 with §7.4, §7.5, §7.8 and §7.10: the structure layout of the elements of
// the container a select's base names -- an unpacked array, a dynamic array, a
// queue or an associative array of structures, declared as a variable or as a
// class property, named bare in a method, through `this` or through a handle,
// `q`, `d`, `this.d`, `h.m`; null for a container of any other elements.
const StructTypeInfo* ContainerElementLayout(const Expr* base, SimContext& ctx);

// §7.2 with §7.5, §7.8 and §7.10: `q[1].green` reads a member of the structure
// an element of a queue, a dynamic, associative or fixed array of structures
// holds, a variable or a class property -- the element read as a select reads
// it, and the member taken out of it by the element type's layout
// (ContainerElementLayout). Built into a name, `q[1]`, the path named no
// variable and read 0. False for an access of any other shape.
bool TryContainerElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

// §7.2.1 with §8.5: the bits a member of a packed structure property
// occupies: the property, the member's lowest bit and its width.
struct PackedMemberBits {
  std::string_view prop;
  uint32_t offset = 0;
  uint32_t width = 0;
};

// §7.2.1 with §8.5: where `access`, `p.hi` or `p.a.b`, names a member of a
// packed structure property the class of `obj` declares, the bits of the
// property the member occupies, into `out`; false for any other expression.
bool PropertyPackedMemberBits(const Expr* access, const ClassObject* obj,
                              SimContext& ctx, PackedMemberBits& out);

// §7.2: the layout of the structure the operand `e` holds: a variable's by
// its name, a class property's or a member's that is itself a structure by
// the member path reaching it; null for any other operand.
const StructTypeInfo* StructLayoutOfOperand(const Expr* e, SimContext& ctx);

// §7.2 with §7.5: where `access` names a member of an unpacked structure
// declared as a dynamic array, `m.data` or `p.h.data`, its elements: to read,
// the array the member holds, an empty one where it holds none; with
// `write`, a copy the member is given to hold in their place
// (DynMemberForWrite). Null for an access of any other member.
QueueObject* ResolveStructDynMember(const Expr* access, SimContext& ctx,
                                    Arena& arena, bool write);

// §7.2: the member of a structure a member access names, the same roots as
// ResolveStructArrayMember takes, whatever the member's type; null where the
// access names no structure member.
const StructFieldInfo* ResolveStructMember(const Expr* access, SimContext& ctx);

// §7.3.2 (printed page 151): a tagged union holds the member's value beside a
// tag naming the member, and §11.9 (printed 304) builds such a value with a
// tagged union expression, `tagged M v`, whose `v` may be a §10.9.2 structure
// assignment pattern to be placed by the named member's own layout rather
// than the union's. The layout of the member `member` names within the union
// laid out by `sinfo`: the nested structure or union layout of the first
// field so named that has one, or null where the union declares no such
// member or the member is a scalar or void with no layout of its own. One
// helper for the three places a `tagged M '{...}` is placed by its member --
// the assignment statement (EvalRhsWithStructContext in
// statement_assign_core.cpp), a subroutine actual (TryEvalTaggedPatternActual
// in eval_function_args_tagged.cpp) and a body local's initializer
// (TaggedPatternMemberLayout in eval_function_body.cpp) -- which each walked
// the union's fields on their own. MemberPathSplit, StructLayoutOfName and
// TagKeyOfName, defined beside this in eval_member_path.cpp, are declared in
// eval_expr_internal.h.
const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member);

// §8.9 (printed page 186): a static property is one variable shared by every
// object of its class and usable with no object, and §8.4 (printed 181-182)
// reads a property of an object through any handle to it, one a static
// property holds included: `C::m_inst.k` from a module, `p::C::m_inst.k`
// through the package (§26.3), and the bare `m_inst.k` a static method
// (§8.10, printed 186) names its own class's static property by. The static
// property the base of such an access names -- the class holding its one
// copy, the copy itself and the property's name.
struct StaticPropertyRef {
  const ClassTypeInfo* owner = nullptr;
  Logic4Vec* slot = nullptr;
  std::string_view name;
};

// The static property `base` names: `C::m` or `p::C::m` for a class the
// scope names (ScopedClassKey), or a bare identifier the running method's
// class, or one lexically enclosing it (§8.23), holds a static property by
// (ClassTypeInfo::StaticPropertyOwner), where no local of the name shadows it
// (NameDenotesVariable); the owner answered is the class declaring the
// property, a base of the named one where that base declares it (§8.13,
// ClassTypeInfo::StaticPropertyDeclarer). False for a base of any other
// shape or name.
bool ResolveStaticPropertyBase(const Expr* base, SimContext& ctx, Arena& arena,
                               StaticPropertyRef& out);

// The object the static property `ref` holds a handle to, and in
// `*declared_key` the key of the class its declaration names
// (PropertyClassName), which scopes a read or a write of a property the
// object's own class shadows (§8.15) and a non-virtual method's dispatch
// (§8.20). Null for a property of no class type -- a structure whose bits
// could equal a live handle's number, an array of handles, a built-in class
// whose handle numbers no ClassObject -- and for a null handle.
ClassObject* StaticPropertyObject(const StaticPropertyRef& ref, SimContext& ctx,
                                  std::string_view* declared_key);

// The static property the innermost base of the member path `access` names,
// with the path of members below it: for `C::m_inst.a.b`, C's m_inst and
// "a.b", the form ResolveClassFieldChain and ResolveClassFieldTarget follow
// into the object. False where `access` is no member access or its base is no
// static property.
bool ResolveStaticHandlePath(const Expr* access, SimContext& ctx, Arena& arena,
                             StaticPropertyRef& ref, std::string& path);

// §8.9 with §8.4: the value of the member path `expr` names through a static
// property's handle -- `C::m_inst.k`, `p::C::m_inst.k`, a static method's
// bare `m_inst.k` -- read on the object the handle refers to. False where the
// base is no static property or the property holds no live object. Asked by
// EvalMemberAccess ahead of the flattened name, which parted `C::m_inst.k`
// at the class into "C" and "m_inst.k", a static property nothing is named,
// and answered a bare `m_inst.k` with no `this` running from no object, so
// each read x where the object's k held 9.
bool TryStaticHandleMember(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);

}  // namespace delta
