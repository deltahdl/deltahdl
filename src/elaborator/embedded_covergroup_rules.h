#ifndef DELTA_ELABORATOR_EMBEDDED_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_EMBEDDED_COVERGROUP_RULES_H

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;

// The rules on the covergroups the class `cls` embeds (§19.4) that turn on
// the class around them, `unit` holding the classes it may extend:
// - a `new` building one in the class's constructor obeys
//   CheckCovergroupNewActuals (§19.3);
// - its expressions read no property local to a class `cls` extends, a
//   derived covergroup inheriting the coverage of one but defining none of
//   its own (§19.4 with §8.18);
// - an instance constant of the class (§8.19) it reads is initialized in the
//   constructor before the statement building it, and not in the same looping
//   statement or fork-join_none as that statement (§19.5).
void CheckEmbeddedCovergroupUses(const ClassDecl* cls,
                                 const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_EMBEDDED_COVERGROUP_RULES_H
