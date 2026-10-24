#pragma once

namespace delta {

struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

// A module's declaration and the compilation unit holding it, the scopes a
// name the module writes is resolved in (§23.9).
struct ModuleInUnit {
  const ModuleDecl& decl;
  const CompilationUnit& unit;
};

// §16.11: the declaration of the task or function the subroutine call `call`,
// attached to a sequence of the module `scope` declares, calls, its name
// resolved as §23.9 and §26.3 resolve one. A name alone, note(v), names a task
// or a function the module declares, a subroutine it imports through DPI
// (§35.5), one a package import of the module makes visible, explicit or
// wildcard, or one the compilation unit declares. A name written through a
// scope, p::note(v), names a subroutine the package `p` declares, or else a
// method of the class `p` (§8.10). A name written through a handle, h.note(v),
// names a method of the class whose handle the module's variable `h` holds, or
// of a class it extends (§8.13); one written through an instance's
// hierarchical name, u.note(v) or u.w.note(v), names a task or function of the
// module or interface instantiated (§23.6). Null where none of them is found,
// a call of a sequence's formal argument among those.
//
// The parser records such a call (ParseAttachedCall in
// src/parser/parser_sequence_match_items.cpp) with the name it calls as its
// `lhs`, an identifier or a member access.
const ModuleItem* AttachedCallTarget(const Expr& call,
                                     const ModuleInUnit& scope);

}  // namespace delta
