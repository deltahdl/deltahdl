#ifndef DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
#define DELTA_ELABORATOR_COVERGROUP_VARIABLES_H

#include <string_view>
#include <vector>

namespace delta {

class Arena;
struct CompilationUnit;
struct CovergroupDecl;
struct DataType;
struct ModuleItem;
struct RtlirModule;
struct RtlirVariable;

const CovergroupDecl* CovergroupNamed(const std::vector<ModuleItem*>& items,
                                      std::string_view name);

const CovergroupDecl* PackageCovergroup(const CompilationUnit* unit,
                                        std::string_view pkg_name,
                                        std::string_view name);

const CovergroupDecl* DeclaredCovergroup(const DataType& dt,
                                         const RtlirModule* mod,
                                         const CompilationUnit* unit);

const CovergroupDecl* VisibleCovergroup(std::string_view name,
                                        const RtlirModule* mod,
                                        const CompilationUnit* unit);

bool UnitDeclaresCovergroup(const CompilationUnit* unit, std::string_view name);

void BindCovergroupVariable(const ModuleItem& item, RtlirVariable& var,
                            RtlirModule* mod, const CompilationUnit* unit,
                            Arena& arena);

}  // namespace delta

#endif
