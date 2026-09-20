#pragma once

#include <string>
#include <string_view>

namespace delta {

class Arena;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct Logic4Vec;
class SimContext;
struct StructTypeInfo;

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
