#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct DataType;
struct SourceLoc;

// §8.13 with §8.25: reports each class whose `extends` clause names no class:
// a name nothing declares, or one only typedefs to a type that is no class
// declare. A name some class, built-in class, or typedef to a named type
// bears is taken as resolving, as is a type parameter, whose type only a
// specialization gives (ReportSpecializationBaseNotClass).
void ReportBasesNamingNoClass(const CompilationUnit& unit, DiagEngine& diag);

// §8.25: where the class the specialization `type` names extends one of its
// own type parameters, reports at `loc` a specialization giving that
// parameter a type that is no class, such as the default `int` of
// `class C #(type P = int) extends P`.
void ReportSpecializationBaseNotClass(const DataType& type, SourceLoc loc,
                                      const CompilationUnit& unit,
                                      DiagEngine& diag);

}  // namespace delta
