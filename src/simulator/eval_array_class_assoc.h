#pragma once

#include <string_view>

namespace delta {

struct AssocArrayObject;
struct ClassDecl;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;
class Arena;

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

// §8.25 with §8.7: the class the property `field` is a handle of on `obj`,
// the property's declaration looked for from the class `from` up its base
// chain as MemberClassTypeName of src/simulator/class_object.h looks: the
// declared type's name where it names a class, else -- `T obj` with T a type
// parameter of the declaring class -- the class the parameter stands for on
// `obj` (TypeParamActual), which a specialization may bind to any class type.
// Empty where the property is of no class type, or names a type parameter
// bound to no class. `obj` may be null, which reads the class's defaults.
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
