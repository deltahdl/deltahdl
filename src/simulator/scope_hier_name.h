#pragma once

#include <string>

namespace delta {

class SimContext;

// §21.2.1.5: the hierarchical name of the scope the running statement stands
// in -- the design element, subroutine, named block or labeled statement that
// contains it. The name starts at the top-level module, walks down the chain
// of instance names recorded on the running process, then through the active
// subroutine, named-block and labeled-statement scopes the statement executor
// tracks in lexical-nesting order. %m expands to it, a severity task's header
// reports it under §20.10, and an immediate cover statement's §16.3 result is
// keyed by it. Empty when no scope is registered at all.
std::string ScopeHierName(const SimContext& ctx);

}  // namespace delta
