#include "elaborator/inline_constraint_scope_resolution.h"

namespace delta {

InlineConstraintBinding ResolveInlineConstraintName(
    InlineConstraintQualifier qualifier, bool declared_in_object_class,
    bool declared_in_local_scope) {
  switch (qualifier) {
    case InlineConstraintQualifier::kThis:
    case InlineConstraintQualifier::kSuper:
      // §18.7.1: this/super anchor resolution at the randomized object's class,
      // regardless of any like-named declaration in the local scope.
      return InlineConstraintBinding::kObjectClassScope;

    case InlineConstraintQualifier::kLocal:
      // §18.7.1: local:: bypasses the object's class scope and resolves the
      // name in the local scope, identically to the unqualified name written
      // there.
      return declared_in_local_scope ? InlineConstraintBinding::kLocalScope
                                     : InlineConstraintBinding::kUnresolved;

    case InlineConstraintQualifier::kNone:
      // §18.7.1: an unqualified name searches the object's class scope first
      // and falls back to the local scope only when the class does not declare
      // it.
      if (declared_in_object_class) {
        return InlineConstraintBinding::kObjectClassScope;
      }
      if (declared_in_local_scope) {
        return InlineConstraintBinding::kLocalScope;
      }
      return InlineConstraintBinding::kUnresolved;
  }
  return InlineConstraintBinding::kUnresolved;
}

bool InlineConstraintQualifierFromToken(TokenKind kind,
                                        InlineConstraintQualifier* out) {
  switch (kind) {
    case TokenKind::kKwLocal:
      *out = InlineConstraintQualifier::kLocal;
      return true;
    case TokenKind::kKwThis:
      *out = InlineConstraintQualifier::kThis;
      return true;
    case TokenKind::kKwSuper:
      *out = InlineConstraintQualifier::kSuper;
      return true;
    default:
      return false;
  }
}

}  // namespace delta
