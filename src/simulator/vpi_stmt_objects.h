#pragma once

#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct Stmt;
struct VpiObject;

// §38.36.1.1 with §37.44: the model's object for the statement `stmt` run in
// the instance `prefix` names, among `stmts`: one a run names with a dot after
// it and the model without, and found under any instance writing it where the
// model keyed it under another name; null where the model holds none.
VpiObject* VpiStmtObjectFor(const VpiStmtObjects& stmts, const Stmt* stmt,
                            std::string prefix);

}  // namespace delta
