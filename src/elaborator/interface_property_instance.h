#pragma once

namespace delta {

class Arena;
class PropertyRegistry;
struct CompilationUnit;
struct ModuleDecl;

// §16.12 with §23.6: a property declared in an interface may be instantiated
// by the hierarchical name of an instance of the interface, `i0.low`, and its
// body is then read in that instance: the clock, the disable condition and the
// boolean name the instance's own ports and variables. For each interface
// instance `decl` holds, this registers under "inst.name" a copy of each
// property of the interface in the clocked boolean form, its free names
// rewritten as members of the instance, so QualifiedInstance and the
// substitution of an instance for the assertion's property_spec reach it.
void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena);

}  // namespace delta
