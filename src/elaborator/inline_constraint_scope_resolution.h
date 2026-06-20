#pragma once

#include <cstdint>

#include "lexer/token.h"

namespace delta {

// §18.7.1: the qualifier that may precede a name referenced inside an inline
// `randomize() with` constraint block, which selects how that name is resolved.
// An unqualified name (kNone) is searched for in two scopes in order; `this`
// and `super` anchor the search at the randomized object's class; the local::
// operator redirects the search to the scope that contains the randomize()
// method call. The local form also covers the special names local::this and
// local::super, which name that local scope's own this/super.
enum class InlineConstraintQualifier : uint8_t {
  kNone,   // an unqualified name in an unrestricted inline constraint block
  kThis,   // this.<name>
  kSuper,  // super.<name>
  kLocal,  // local::<name>, including local::this and local::super
};

// §18.7.1: the scope a referenced name binds to once resolved.
// kObjectClassScope is the class of the object handle on which randomize() with
// was called; kLocalScope is the scope containing that method call. kUnresolved
// reports a name that is found in neither of the searched scopes.
enum class InlineConstraintBinding : uint8_t {
  kObjectClassScope,
  kLocalScope,
  kUnresolved,
};

// §18.7.1: resolve one name referenced inside an unrestricted inline constraint
// block to the scope it binds to, given which of the two candidate scopes
// declares it.
//
//   - An unqualified name (kNone) is sought in the randomized object's class
//     scope first and, only if absent there, in the local (method-call) scope;
//     it is unresolved when neither declares it.
//   - A name qualified by this/super binds to the object's class scope.
//   - A name qualified by local:: is resolved in the local scope alone, so that
//     local::a denotes the same declaration as the unqualified a written
//     directly in the local scope. local::obj — the object handle of an
//     obj.randomize() with call — is one such local-scope name; it resolves
//     there to the handle that designates the randomized object.
//
// `declared_in_object_class` and `declared_in_local_scope` report whether each
// scope declares the bare name. The special names this and super always exist
// in a scope, so a caller resolving local::this or local::super passes
// declared_in_local_scope = true.
InlineConstraintBinding ResolveInlineConstraintName(
    InlineConstraintQualifier qualifier, bool declared_in_object_class,
    bool declared_in_local_scope);

// §18.7.1: map the keyword or operator that prefixes a name in an inline
// constraint to its qualifier category. The `local` keyword (the local::
// operator) and the `this` and `super` keywords are recognized; any other token
// does not introduce a qualifier, so the name is unqualified. Returns false in
// that case and leaves *out untouched.
bool InlineConstraintQualifierFromToken(TokenKind kind,
                                        InlineConstraintQualifier* out);

}  // namespace delta
