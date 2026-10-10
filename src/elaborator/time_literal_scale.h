#pragma once

#include "common/types.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct PackageDecl;

// §3.14.2.3 (printed page 60): the time unit and precision of a time scope,
// each taken from the first of its sources that gives one.

// The compilation-unit scope of `unit`: its own timeunit and timeprecision
// declarations, else the 1 ns / 1 ns default TimeScale holds.
TimeScale CompilationUnitTimescale(const CompilationUnit& unit);

// The module, interface, program or checker `decl` of `unit`: its own
// declarations; for one nested in another (§23.4), the enclosing one's,
// whatever source that took them from; for one written outside every other,
// the `timescale before its header, else the compilation unit's.
TimeScale ModuleTimescale(const ModuleDecl* decl, const CompilationUnit& unit);

// The package `pkg`, whose compilation-unit scope gives `unit_scale`: its own
// declarations, else the `timescale before its header, else `unit_scale`. A
// package is never nested, so no enclosing element stands ahead of those.
TimeScale PackageTimescale(const PackageDecl& pkg, const TimeScale& unit_scale);

// §5.8: scales each time literal `unit` recorded (CompilationUnit::
// time_literals) to the time unit of the scope it is written in, magnitude
// included, now that the `timescale before each element has reached it.
void ScaleTimeLiterals(const CompilationUnit& unit);

}  // namespace delta
