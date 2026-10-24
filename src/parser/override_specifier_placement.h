#pragma once

namespace delta {

class DiagEngine;
struct ModuleItem;

// Footnote 25 of Syntax 13-1 in §13.3 and of Syntax 13-2 in §13.4, given again
// for A.2.6 and A.2.7: dynamic_override_specifiers are legal only on a method
// declared inside the scope of a class that is not an interface class. Reports
// the ones `item`, a task or function declared anywhere else, carries: a
// module's, an interface's, a program's, a package's or the compilation unit's
// subroutine, a definition written outside its class or through an interface
// prefix, or a modport's prototype. A task's report cites §13.3 and a
// function's §13.4, the clauses printing the footnote for each.
void ReportMisplacedOverrideSpecifiers(const ModuleItem& item,
                                       DiagEngine& diag);

}  // namespace delta
