#include <gtest/gtest.h>

#include "elaborator/rewrite_item.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §F.4: item is not a SystemVerilog function; it exists only inside the
// rewriting algorithm.
TEST(RewriteItem, NotASystemVerilogFunction) {
  EXPECT_FALSE(ItemExpr::IsSystemVerilogFunction());
}

// §F.4: item(e) behaves like e in all respects, so the wrapper must
// preserve identity of the wrapped node so downstream lowering can still
// reach the original expression.
TEST(RewriteItem, WrapperRetainsWrappedExpression) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kTypedExpr);
  EXPECT_EQ(wrapped.Wrapped(), &e);
  EXPECT_TRUE(wrapped.BehavesLikeWrapped());
}

// §F.4: item may be applied to any SystemVerilog expression that may
// appear as an actual argument in a named-sequence/property/checker/let
// instance. Exercise a variety of expression shapes (identifier, cast,
// binary, call) to observe that the wrapper accepts the breadth the
// rewriting algorithm needs.
TEST(RewriteItem, WrapsVariedExpressionShapes) {
  Expr ident{};
  ident.kind = ExprKind::kIdentifier;
  Expr cast{};
  cast.kind = ExprKind::kCast;
  Expr bin{};
  bin.kind = ExprKind::kBinary;
  Expr call{};
  call.kind = ExprKind::kCall;
  for (const Expr* node : {&ident, &cast, &bin, &call}) {
    auto wrapped = ItemExpr::Wrap(node, ItemOperandKind::kTypedExpr);
    EXPECT_EQ(wrapped.Wrapped(), node);
    EXPECT_TRUE(wrapped.Admits(ItemOperation::kNamedItemOfTypeOp));
  }
}

// §F.4: sequence-instance operations are admitted on item(e) when e is a
// sequence.
TEST(RewriteItem, SequenceKindAdmitsSequenceInstanceOperations) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kSequence);
  EXPECT_TRUE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  // Sequences are not properties, so property-instance ops remain
  // outside what item admits here.
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

// §F.4: property-instance operations are admitted on item(e) when e is a
// property, and the text spells out that top-level properties are
// included.
TEST(RewriteItem, PropertyAndTopLevelPropertyAdmitPropertyInstanceOperations) {
  Expr e{};
  auto wrapped_prop = ItemExpr::Wrap(&e, ItemOperandKind::kProperty);
  EXPECT_TRUE(wrapped_prop.Admits(ItemOperation::kPropertyInstanceOp));
  auto wrapped_top = ItemExpr::Wrap(&e, ItemOperandKind::kTopLevelProperty);
  EXPECT_TRUE(wrapped_top.Admits(ItemOperation::kPropertyInstanceOp));
  // Properties do not admit sequence-instance operations through item.
  EXPECT_FALSE(wrapped_prop.Admits(ItemOperation::kSequenceInstanceOp));
}

// §F.4: a typed expression that is neither a sequence nor a property
// should not pick up sequence- or property-instance operations from
// item; the named-item-of-type extension is the only one it gets.
TEST(RewriteItem, PlainTypedExprDoesNotPickUpSequenceOrPropertyOps) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kTypedExpr);
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

// §F.4: the named-item-of-type extension is keyed on having a defined
// type, not on the typed-expression kind specifically. Sequences and
// properties (top-level or not) carry types and so must also pick up
// the named-item-of-type operations through item.
TEST(RewriteItem, DefinedTypeKindsAdmitNamedItemOfTypeOperations) {
  Expr e{};
  for (auto kind : {ItemOperandKind::kSequence, ItemOperandKind::kProperty,
                    ItemOperandKind::kTopLevelProperty}) {
    auto wrapped = ItemExpr::Wrap(&e, kind);
    EXPECT_TRUE(wrapped.Admits(ItemOperation::kNamedItemOfTypeOp));
  }
}

// §F.4 last sentence: for expressions with undefined types, item does
// not enable additional operations of any class.
TEST(RewriteItem, UndefinedTypeAdmitsNothing) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kUndefinedType);
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kNamedItemOfTypeOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

}  // namespace
