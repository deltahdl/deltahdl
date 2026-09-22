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

namespace delta {

class Arena;
class SimContext;
struct ClassTypeInfo;
struct DataType;

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

}  // namespace delta
