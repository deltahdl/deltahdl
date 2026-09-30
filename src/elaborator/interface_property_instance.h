#pragma once

#include <vector>

namespace delta {

class Arena;
class PropertyRegistry;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

// The declarations of the module being elaborated that the run looks an
// instance up among, its properties and its sequences.
struct RunDeclarations {
  std::vector<ModuleItem*>& properties;
  std::vector<ModuleItem*>& sequences;
};

// §16.12 with §23.6: a property declared in an interface may be instantiated
// by the hierarchical name of an instance of the interface, `i0.low`, and its
// body is then read in that instance: the clock, the disable condition and the
// boolean name the instance's own ports and variables. For each interface
// instance `decl` holds, this registers under "inst.name" a copy of each
// property of the interface, its free names rewritten as members of the
// instance, so QualifiedInstance and the substitution of an instance for the
// assertion's property_spec reach it. A copy whose body is a tree, which the
// run expands where an attempt reaches the instance, is also appended to
// `run.properties`. §16.8: each sequence of the interface is copied and
// registered the same way, and appended to `run.sequences`, so `u.s` is
// flattened from the copy wherever it is instantiated.
void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena, RunDeclarations run);

}  // namespace delta
