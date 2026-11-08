#pragma once

#include <string_view>
#include <vector>

namespace delta {

struct ClassDecl;
struct DataType;
struct PackageDecl;
struct RtlirDesign;
struct RtlirModule;

int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name);

int VpiPackageNamedTypeVariableKind(const RtlirDesign& design,
                                    const PackageDecl* package,
                                    std::string_view name);

int VpiScopedTypeVariableKind(const RtlirDesign& design,
                              std::string_view package, const DataType& type);

std::vector<ClassDecl*> VpiPackageClasses(const PackageDecl& package);

}  // namespace delta
