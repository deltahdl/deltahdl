#pragma once

#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct Expr;
struct Stmt;
struct VpiObject;

VpiObject* VpiStmtObjectFor(const VpiStmtObjects& stmts, const Stmt* stmt,
                            std::string prefix);

VpiObject* VpiCallSiteObjectFor(const VpiCallSiteObjects& sites,
                                const Expr* call_site, std::string prefix);

}  // namespace delta
