#pragma once

#include <string_view>
#include <vector>

namespace delta {

struct ClassDecl;
struct DataType;
struct PackageDecl;
struct RtlirDesign;
struct RtlirModule;

// §6.18 with §8.3: the object kind of a variable an instance of `mod` declares
// with a type standing for `name`: a class var for a class the module or the
// compilation unit declares, a built-in class or a typedef whose chain of
// names ends in a class, and for any other typedef the kind of the type at the
// end of its chain; a logic var for a name nothing resolves.
int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name);

// §6.18 with §8.3 and §26.3: the same for a variable the package `package`
// declares, or the compilation unit where `package` is null: a class var for a
// class the package or the compilation unit declares, a built-in class or a
// typedef whose chain of names ends in a class, and for any other typedef the
// kind of the type at the end of its chain, a package's typedef found under
// its qualified name `p::t`; a logic var for a name nothing resolves.
int VpiPackageNamedTypeVariableKind(const RtlirDesign& design,
                                    const PackageDecl* package,
                                    std::string_view name);

// §6.18 with §26.3: the same for a variable the package named `package`
// declares with the named type `type`, or the compilation unit where `package`
// names none (empty among them); a package's name written before the type's,
// `a::t`, resolves it in that package instead. A scope naming no package,
// `$unit::t`, resolves in the compilation unit, whose typedefs are recorded
// under their bare names as well.
int VpiScopedTypeVariableKind(const RtlirDesign& design,
                              std::string_view package, const DataType& type);

// §26.2: the classes the package `package` declares, in the order written.
std::vector<ClassDecl*> VpiPackageClasses(const PackageDecl& package);

}  // namespace delta
