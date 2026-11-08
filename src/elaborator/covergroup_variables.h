#ifndef DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
#define DELTA_ELABORATOR_COVERGROUP_VARIABLES_H

#include <string_view>

namespace delta {

class Arena;
struct CompilationUnit;
struct CovergroupDecl;
struct ModuleItem;
struct RtlirModule;
struct RtlirVariable;

const CovergroupDecl* VisibleCovergroup(std::string_view name,
                                        const RtlirModule* mod,
                                        const CompilationUnit* unit);

bool UnitDeclaresCovergroup(const CompilationUnit* unit, std::string_view name);

void BindCovergroupVariable(const ModuleItem& item, RtlirVariable& var,
                            RtlirModule* mod, const CompilationUnit* unit,
                            Arena& arena);

}  // namespace delta

#endif
