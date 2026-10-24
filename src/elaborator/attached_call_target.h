#pragma once

namespace delta {

struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

// §16.11: the declaration of the task or function the subroutine call `call`,
// attached to a sequence of `decl`, calls, its name resolved as §23.9 and
// §26.3 resolve one. A name alone, note(v), names a task or a function `decl`
// declares, a subroutine it imports through DPI (§35.5), one a package import
// of `decl` makes visible, explicit or wildcard, or one the compilation unit
// declares. A name written through a scope, p::note(v), names a subroutine
// the package `p` declares, or else a method of the class `p` (§8.10). A name
// written through a handle, h.note(v), names a method of the class whose
// handle the module's variable `h` holds, or of a class it extends (§8.13).
// Null where none of them is found, a call of a task through an instance's
// name or of a sequence's formal argument among those.
//
// The parser records such a call (ParseAttachedCall in
// src/parser/parser_sequence_match_items.cpp) with the name it calls as its
// `lhs`, an identifier or a member access.
const ModuleItem* AttachedCallTarget(const Expr& call, const ModuleDecl& decl,
                                     const CompilationUnit& unit);

}  // namespace delta
