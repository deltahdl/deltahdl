#pragma once

#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct Expr;
struct Stmt;
struct VpiObject;

// §38.36.1.1 with §37.44: the model's object for the statement `stmt` run in
// the instance `prefix` names, among `stmts`: one a run names with a dot after
// it and the model without, and found under any instance writing it where the
// model keyed it under another name; null where the model holds none.
VpiObject* VpiStmtObjectFor(const VpiStmtObjects& stmts, const Stmt* stmt,
                            std::string prefix);

// §37.42 detail 3 and §37.43 detail 6: the model's object for the call
// `call_site` written in the instance `prefix` names; null where the model
// holds no call there. Another instance's call is that instance's, not this
// one. A run names an instance with a dot after it and the model without. A
// body a package or the compilation unit declares runs in whichever instance
// calls it, and its calls are kept under the package's name or `$unit` alone
// (AttachPackageSubroutineBodies), so a call site the model holds under one
// scope only is that call wherever it runs.
VpiObject* VpiCallSiteObjectFor(const VpiCallSiteObjects& sites,
                                const Expr* call_site, std::string prefix);

}  // namespace delta
