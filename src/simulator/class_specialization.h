#pragma once

// §8.25 (printed page 204 of IEEE 1800-2023): a specialization is a generic
// class together with one set of actual parameter values, each specialization
// has its own set of static member variables, and a generic class is not a
// type at all -- only a specialization is. The lowerer registers one
// ClassTypeInfo per class declaration (Lowerer::RegisterClassDecl in
// lowerer_class.cpp), which is the generic class rather than any type, and its
// static_properties map is therefore one map shared by every specialization:
// a `static int count` bumped in new() counts every object of every
// specialization, and a `static const int W = size` holds whatever the default
// specialization's parameter gave it. This is where a specialization gets a
// ClassTypeInfo of its own, so that the map, and the class parameters stored
// beside it, belong to the one set of actuals rather than to the declaration.

#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct ClassTypeInfo;
struct DataType;
struct Expr;

// The class type for `generic` specialized by `actuals`, registered under a
// key that spells the actuals -- `vector#(4)` -- and created on the first
// request for that key. §8.25 makes two parameter sets distinct unless every
// parameter matches, so equal actuals answer the one type and unequal actuals
// answer different ones, which is what the key spells.
//
// `generic` itself is answered where it names no class declaration or where
// `actuals` is empty, the latter being §8.25.1's default specialization, whose
// parameters the declaration's own defaults already gave it.
//
// Where the extends clause names one of the class's own type parameters,
// `class D #(type B = P) extends B;`, the specialization extends the class its
// own actual binds that parameter to rather than the default's, §8.25 letting
// a type parameter name the base and making each specialization a type of its
// own. Where it writes a `#(...)` list, `class D3 #(type P = real) extends C
// #(P);`, the specialization extends the specialization of the base that list
// names once the class's own parameters in it are replaced by its actuals
// (ActualsUnderSpecialization), and so reads that specialization's static
// member variables rather than the base declaration's.
ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena);

// §8.25 (printed page 204 of IEEE 1800-2023): a type parameter used in a type
// resolves to a type only after elaboration, so a list of actuals naming a
// type parameter of the class that writes it names a different specialization
// in each specialization of that class: a class-scope typedef, UVM's
// `typedef uvm_object_registry#(T,Tname) this_type;`, and an extends clause,
// `class D3 #(type P = real) extends C #(P);`. These are the actuals `written`
// with each such name replaced by the type `holder` binds it to, `Box#(T)`
// becoming Box#(byte) under Reg#(byte); the name a named actual was written
// with is kept, the substitution being of the type alone. An actual naming a
// class-scope typedef of `holder` (§8.3), UVM's `this_type`, is spelled by the
// name the run holds that typedef's class under, the name being `holder`'s
// and not the specialized class's. A type parameter comes back as written
// where the holder binds nothing, which is the class declaration's own type.
std::vector<DataType> ActualsUnderSpecialization(
    const ClassTypeInfo* holder, const std::vector<DataType>& written,
    SimContext& ctx);

// §8.25 with §8.23: a type parameter stands for the type its actual gives,
// so a scope form whose prefix is a type parameter of the running method's
// class, UVM's `Tregistry::get()` in uvm_registry_common#(Tregistry, ...),
// names the class that actual names -- a different one under each
// specialization of the running class. That class, specialized by the list
// the actual writes, or the class itself where it writes none; null where
// `name` is no type parameter of the running class, where no method is
// running, and where the actual names no class.
ClassTypeInfo* ClassNamedByTypeParam(std::string_view name, SimContext& ctx,
                                     Arena& arena);

// Defined in lowerer_class.cpp, beside the static initialization of a class
// declaration, and called on each specialization as it is created. §8.9: each
// static property's one copy takes its initializer once; a specialization's
// copy is its own, and takes it with that specialization's value parameters
// bound, so an initializer naming one reads the actual rather than nothing.
void InitSpecializationStaticProperties(ClassTypeInfo* spec, SimContext& ctx,
                                        Arena& arena);

// The specialization the left side of a scope form names, the `vector#(4)` of
// `vector#(4)::count` and of `vector#(4)::get()`: §8.25.1 has the explicit
// form name one specialization, and §8.25 makes that specialization a type of
// its own carrying its own set of static member variables. Interned on the
// call where nothing has interned it already, a scope form being able to be
// the whole of what names a specialization. An actual in the list that
// names a type parameter of the running method's class stands for the type
// the running specialization binds it to, §8.25 resolving a type parameter
// used in a type only after elaboration: `Box#(T)::` inside `Reg #(type T)`
// names Box#(byte) under Reg#(byte).
//
// §8.25.1 also lets the prefix be the unadorned name, inside the named class
// alone, where it refers to the members of the class in hand rather than
// denoting the default specialization: such a `base` names the specialization
// the running method belongs to, `counter::count` inside a method reached
// through `counter#(4)::` being that specialization's count.
//
// Null where `base` is no identifier, where the identifier names no class
// declaration, and where an unadorned one names a class no running method
// belongs to a specialization of.
ClassTypeInfo* ScopeNamedSpecialization(const Expr* base, SimContext& ctx,
                                        Arena& arena);

// The static property `expr` reads through a specialization scope,
// `vector#(1)::count`: true with `out` filled where `expr` is a member
// select whose left side names a specialization as ScopeNamedSpecialization
// reads it, and that specialization or one of its bases declares a static
// property of that name. §8.25.1 has the scope form name
// one specialization,
// and §8.25 gives each specialization its own set of static member variables,
// so the read is of that specialization's copy rather than of the
// declaration's one map. The specialization is interned on the read where
// nothing has interned it already, which is what `V#(4)::W` needs: a scope
// form can be the whole of what names a specialization, no variable of it
// ever being declared.
//
// False for a parameter of the class, whose value the list carries rather
// than the specialization's storage, and which is read before this.
bool TryScopeSpecializationStaticMember(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out);

}  // namespace delta
