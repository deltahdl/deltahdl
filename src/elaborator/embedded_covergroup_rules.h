#ifndef DELTA_ELABORATOR_EMBEDDED_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_EMBEDDED_COVERGROUP_RULES_H

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;

void CheckEmbeddedCovergroupUses(const ClassDecl* cls,
                                 const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif
