#include <gtest/gtest.h>

#include "elaborator/inline_constraint_scope_resolution.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// §18.7.1 (C1): an unqualified name in an unrestricted inline constraint block
// is searched for in the randomized object's class scope first. When the class
// declares it, the name binds there even if the local scope also declares it.
TEST(InlineConstraintScopeResolution, UnqualifiedPrefersObjectClassScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kNone,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kObjectClassScope);
}

// §18.7.1 (C1): an unqualified name not declared by the object's class falls
// through to the local (method-call) scope.
TEST(InlineConstraintScopeResolution, UnqualifiedFallsBackToLocalScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kNone,
                                        /*declared_in_object_class=*/false,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kLocalScope);
}

// §18.7.1 (C1): an unqualified name absent from both candidate scopes resolves
// nowhere.
TEST(InlineConstraintScopeResolution, UnqualifiedUnresolvedWhenAbsent) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kNone,
                                        /*declared_in_object_class=*/false,
                                        /*declared_in_local_scope=*/false),
            InlineConstraintBinding::kUnresolved);
}

// §18.7.1 (C3): a name qualified by this binds to the randomized object's class
// scope, taking that scope even when the local scope also declares the name.
TEST(InlineConstraintScopeResolution, ThisBindsToObjectClassScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kThis,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kObjectClassScope);
}

// §18.7.1 (C3): super behaves as this does for the purpose of choosing the
// scope — it anchors at the object's class scope.
TEST(InlineConstraintScopeResolution, SuperBindsToObjectClassScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kSuper,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kObjectClassScope);
}

// §18.7.1 (C4 / C6 / C5): local:: bypasses the object's class scope and resolves
// the name in the local scope — even when the object's class also declares the
// name — so local::a denotes the same declaration as the unqualified a in the
// local scope. Resolution depends only on the qualifier and the local-scope
// declaration, never on what the name denotes, so this same call also stands for
// C5: a local:: name resolves identically whether it is a variable, a type, or a
// class scope.
TEST(InlineConstraintScopeResolution, LocalQualifierBindsToLocalScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kLocal,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kLocalScope);
}

// §18.7.1 (C4 / C7): the special name local::this names the local scope's own
// this, so it resolves to the local scope. A caller treats this/super as always
// present in a scope, here passing declared_in_local_scope = true. The same call
// also models C7: for an obj.randomize() with call the object handle obj is
// itself a local-scope name, so local::obj likewise resolves in the local scope.
TEST(InlineConstraintScopeResolution, LocalThisBindsToLocalScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kLocal,
                                        /*declared_in_object_class=*/false,
                                        /*declared_in_local_scope=*/true),
            InlineConstraintBinding::kLocalScope);
}

// §18.7.1 (C4 / C6): because local:: searches only the local scope, a name the
// local scope does not declare is unresolved even when the object's class
// declares it — local:: never reaches the class scope.
TEST(InlineConstraintScopeResolution, LocalQualifierIgnoresObjectClassScope) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kLocal,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/false),
            InlineConstraintBinding::kUnresolved);
}

// §18.7.1 (C1): when only the object's class declares an unqualified name, it
// binds there — the object-class scope is searched first, so its match settles
// the name without the local scope needing to declare it.
TEST(InlineConstraintScopeResolution, UnqualifiedBindsObjectClassWhenLocalAbsent) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kNone,
                                        /*declared_in_object_class=*/true,
                                        /*declared_in_local_scope=*/false),
            InlineConstraintBinding::kObjectClassScope);
}

// §18.7.1 (C2 / C4): local:: searches only the local scope, so a local:: name
// declared in neither scope is unresolved — the object-class scope is never
// consulted to rescue it.
TEST(InlineConstraintScopeResolution, LocalQualifierUnresolvedWhenAbsentEverywhere) {
  EXPECT_EQ(ResolveInlineConstraintName(InlineConstraintQualifier::kLocal,
                                        /*declared_in_object_class=*/false,
                                        /*declared_in_local_scope=*/false),
            InlineConstraintBinding::kUnresolved);
}

// §18.7.1: the qualifier keywords/operators that may head a name in an inline
// constraint map to their categories; local is the local:: operator, and this
// and super are keywords.
TEST(InlineConstraintScopeResolution, QualifierTokenMapping) {
  InlineConstraintQualifier q{};
  ASSERT_TRUE(InlineConstraintQualifierFromToken(TokenKind::kKwLocal, &q));
  EXPECT_EQ(q, InlineConstraintQualifier::kLocal);
  ASSERT_TRUE(InlineConstraintQualifierFromToken(TokenKind::kKwThis, &q));
  EXPECT_EQ(q, InlineConstraintQualifier::kThis);
  ASSERT_TRUE(InlineConstraintQualifierFromToken(TokenKind::kKwSuper, &q));
  EXPECT_EQ(q, InlineConstraintQualifier::kSuper);
}

// A token that is not a qualifier keyword leaves the name unqualified; the
// mapping reports no qualifier.
TEST(InlineConstraintScopeResolution, QualifierTokenMappingRejectsNonQualifier) {
  InlineConstraintQualifier q = InlineConstraintQualifier::kLocal;
  EXPECT_FALSE(InlineConstraintQualifierFromToken(TokenKind::kPlus, &q));
  EXPECT_FALSE(InlineConstraintQualifierFromToken(TokenKind::kIdentifier, &q));
}

}  // namespace
