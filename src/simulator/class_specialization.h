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
ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena);

// Defined in lowerer_class.cpp, beside the static initialization of a class
// declaration, and called on each specialization as it is created. §8.9: each
// static property's one copy takes its initializer once; a specialization's
// copy is its own, and takes it with that specialization's value parameters
// bound, so an initializer naming one reads the actual rather than nothing.
void InitSpecializationStaticProperties(ClassTypeInfo* spec, SimContext& ctx,
                                        Arena& arena);

// The static property `expr` reads through a specialization scope,
// `vector#(1)::count`: true with `out` filled where `expr` is a member
// select whose left side is an identifier carrying a `#(...)` list, that
// identifier names a class declaration, and the class or one of its bases
// declares a static property of that name. §8.25.1 has the scope form name
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
