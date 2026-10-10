#pragma once

#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct Stmt;

// A named block's label with where its block begins.
using BlockLabel = std::pair<std::string_view, SourceLoc>;

// §3.13 (f) (printed page 58): a named or unnamed block opens a block name
// space, and the label of a named block is declared in the name space of the
// construct enclosing it. Appends to `out` the label of each named begin-end
// or fork-join block that `s` is, or holds without passing through another
// block: a statement that is not a block opens no name space, so the blocks
// written under an if, a loop or a timing control stand in the name space the
// statement does.
void CollectNameSpaceLabels(const Stmt* s, std::vector<BlockLabel>& out);

// §3.13 (f): one block name space, the statement list `stmts` of a block or of
// a function or task body, unifies its variables and parameters, its
// user-defined types and its named blocks, beside `names` already declared
// there -- a subroutine's formal arguments, which are declared in its scope.
// Reports each declaration of a name already declared in it.
void CheckBlockNameSpace(const std::vector<Stmt*>& stmts,
                         std::unordered_set<std::string_view> names,
                         DiagEngine& diag);

// §3.13 (f): every begin-end and fork-join block `s` is or holds, at any
// depth, opens a block name space of its own, checked by CheckBlockNameSpace;
// a name reused in a nested block is that block's own, legal shadowing rather
// than a redeclaration.
void CheckNestedBlockNameSpaces(const Stmt* s, DiagEngine& diag);

}  // namespace delta
