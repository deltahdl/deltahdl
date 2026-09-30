#pragma once

namespace delta {

class Arena;
struct CompilationUnit;

// §26.3 with §16.8 and §16.12: a name in the declaration of a package's
// sequence or property is resolved in the package's scope, wherever the
// declaration is instantiated from. For each package of `unit`, this makes
// each name the body, the clock, the disable condition or a default of one
// of its sequences or properties gives to a sequence, property, parameter,
// variable, function or let of the package, a formal or a local of its own
// aside, the package-scoped name `pk::name`, which the elaborator and the
// run resolve from every scope whether it imports the package or not; and it
// makes each sequence so named in a property's body a sequence there.
void ResolvePackageAssertionNames(const CompilationUnit* unit, Arena& arena);

}  // namespace delta
