#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct DataType;
struct SourceLoc;

void ReportBasesNamingNoClass(const CompilationUnit& unit, DiagEngine& diag);

void ReportSpecializationBaseNotClass(const DataType& type, SourceLoc loc,
                                      const CompilationUnit& unit,
                                      DiagEngine& diag);

}  // namespace delta
