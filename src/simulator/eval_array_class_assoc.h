#pragma once

#include <string_view>

namespace delta {

struct AssocArrayObject;
struct ClassMember;
struct ClassDecl;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct ModuleItem;
struct Stmt;
class SimContext;
class Arena;

// §6.18 with §8.3 (printed page 180 of IEEE 1800-2023): a typedef is a class
// item, seen from `from`, its bases (§8.13) and the classes enclosing it
// (§8.23). The typedef item the nearest of them declares under `name`; null
// where none does, or where `from` is null.
const ModuleItem* ClassScopeTypedefItem(const ClassTypeInfo* from,
                                        std::string_view name);

// §6.18 with §26.3: the typedef item the written type `type` names, seen from
// the class `from`: one the class scope `C::` or the package `p::` qualifying
// it declares, else one of `from`'s class scope (ClassScopeTypedefItem), of
// the package `from` is declared in, or of the compilation unit, nearest
// first. Null where `type` names no typedef.
const ModuleItem* TypedefItemSeenFrom(const DataType& type,
                                      const ClassTypeInfo* from,
                                      SimContext& ctx);

// §7.4.4 with §8.5: the typedef that gives the property `member` of
// `declaring` its unpacked dimensions -- the one its type names
// (TypedefItemSeenFrom) where the declaration writes none of its own and the
// typedef writes some; null otherwise.
const ModuleItem* PropertyTypedefItem(const ClassMember* member,
                                      const ClassTypeInfo* declaring,
                                      SimContext& ctx);

// §6.18 with §7.4.4 and §8.3: a declaration in a method's body whose type names
// a class-scope typedef, bare as `edges_t e;` from the declaring class's own
// methods or through the class scope as `uvm_phase::edges_t edges;` from
// anywhere, declares an object of the type the typedef stands for, the
// typedef's unpacked dimensions included. The elaborator gives a module
// procedure's declaration a typedef's dimensions (AdoptTypedefDimsInStmt) and
// reaches neither a class's method bodies nor its typedefs, so such a local
// was a scalar of the element type: uvm_phase_hopper::sync_phase's `edges`
// held no predecessor and its foreach ran once with a null key. The
// declaration `stmt` with the typedef's element type and dimensions written
// on it, built once per declaration; `stmt` itself where it writes dimensions
// of its own or names no such typedef.
const Stmt* DeclShapedByClassTypedef(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

// §7.8/§8.5: a class property declared with an associative dimension, `int
// count[severity_t]`, is an associative array of the object: §8.5 puts no
// restriction on a property's data type, and §7.8 has the array allocate no
// storage until an element is first written and then keep the entries that
// have been assigned. The object holds one AssocArrayObject per such property
// (ClassObject::assoc_properties), and a static one is the class's
// (ClassTypeInfo::static_assoc_properties, §8.9), each built on the first
// reference to the property with the element width and index type its
// declaration gives it.
//
// The array named `name` on the class chain from `from` -- the property's
// declaration is looked for from that class upward, so an unqualified name in
// a method is resolved in the enclosing class's scope (§8.15) -- held by `obj`,
// or by the declaring class where the property is static, in which case `obj`
// may be null. Null where no class of the chain declares `name` as a property
// with one dimension that IsAssocIndexDim answers for.
AssocArrayObject* ClassAssocProperty(ClassObject* obj,
                                     const ClassTypeInfo* from,
                                     std::string_view name, SimContext& ctx);

// The associative array the bare name `name` designates where it is written:
// the declared array SimContext::FindAssocArray knows under the name, else --
// where no variable, queue or fixed array of the name shadows it -- the
// property of the running method's object (§8.11) or of its class (§8.10).
// `owner` receives the object whose property answered, or null where the
// array is a declared one or a static property, so a writer knows which
// watchers §9.4.2 has it tell.
AssocArrayObject* FindAssocArrayOfName(std::string_view name, SimContext& ctx,
                                       ClassObject** owner = nullptr);

// The associative array the expression `base` designates, as the base of an
// element select, the receiver of a method call or the left of a member
// access: a bare name as FindAssocArrayOfName reads it, `this.name` and
// `handle.name` naming the property of the object the handle refers to, and
// `C::name` a static property of class C. `owner` as above. Null where `base`
// is of no such shape or names no associative array.
AssocArrayObject* FindAssocArrayOfBase(const Expr* base, SimContext& ctx,
                                       Arena& arena,
                                       ClassObject** owner = nullptr);

// §8.25: the type the type parameter `pname` of `decl` stands for on `obj`:
// the actual the object's specialization bound it to, else the default the
// class declares for it (§8.25.1's default specialization), else null for a
// parameter the class gives no default. Shared with the queue property of
// src/simulator/eval_array_class_queue.h, whose element type may name one.
const DataType* TypeParamActual(const ClassObject* obj, const ClassDecl* decl,
                                std::string_view pname);

// §8.25 with §8.7: the key the run holds the class the property `field` is a
// handle of on `obj` under, the property's declaration looked for from the
// class `from` up its base chain as MemberClassTypeName of
// src/simulator/class_object.h looks: the class the declared type names as
// written in the declaring class (DeclaredClassKeyInScope of
// declared_class_key.h, so §8.23's `Outer::Inner h` in another class and
// `Inner h` in Outer both answer `Outer::Inner`), else -- `T obj` with T a
// type parameter of the declaring class -- the class the parameter stands for
// on `obj` (TypeParamActual), which a specialization may bind to any class
// type. Empty where the property is of no class type, or names a type
// parameter bound to no class. `obj` may be null, which reads the class's
// defaults. Resolved by the bare type name alone, `x.h = new` on
// `Outer::Inner h` constructed nothing and an array property `Outer::Inner
// kids[2]` held plain values.
std::string_view PropertyClassName(const ClassObject* obj,
                                   const ClassTypeInfo* from,
                                   std::string_view field, SimContext& ctx);

// Whether `expr` is a path of names to an object -- an identifier, `this`
// among them, or a member access down such a path -- which is evaluated to a
// handle without running anything. A call or a select on the way is not, and
// is left to the paths that own it rather than evaluated here and again there.
bool IsHandlePath(const Expr* expr);

// The object a member access's handle side names: the running method's object
// for `this` (§8.11), else the object the handle the side evaluates to refers
// to; null for a side that is no handle path or a null handle.
ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena);

}  // namespace delta
