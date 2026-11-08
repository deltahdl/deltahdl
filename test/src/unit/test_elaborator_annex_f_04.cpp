#include <gtest/gtest.h>

#include "elaborator/rewrite_item.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(RewriteItem, NotASystemVerilogFunction) {
  EXPECT_FALSE(ItemExpr::IsSystemVerilogFunction());
}

TEST(RewriteItem, WrapperRetainsWrappedExpression) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kTypedExpr);
  EXPECT_EQ(wrapped.Wrapped(), &e);
  EXPECT_TRUE(wrapped.BehavesLikeWrapped());
}

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

TEST(RewriteItem, SequenceKindAdmitsSequenceInstanceOperations) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kSequence);
  EXPECT_TRUE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

TEST(RewriteItem, PropertyAndTopLevelPropertyAdmitPropertyInstanceOperations) {
  Expr e{};
  auto wrapped_prop = ItemExpr::Wrap(&e, ItemOperandKind::kProperty);
  EXPECT_TRUE(wrapped_prop.Admits(ItemOperation::kPropertyInstanceOp));
  auto wrapped_top = ItemExpr::Wrap(&e, ItemOperandKind::kTopLevelProperty);
  EXPECT_TRUE(wrapped_top.Admits(ItemOperation::kPropertyInstanceOp));
  EXPECT_FALSE(wrapped_prop.Admits(ItemOperation::kSequenceInstanceOp));
}

TEST(RewriteItem, PlainTypedExprDoesNotPickUpSequenceOrPropertyOps) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kTypedExpr);
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

TEST(RewriteItem, DefinedTypeKindsAdmitNamedItemOfTypeOperations) {
  Expr e{};
  for (auto kind : {ItemOperandKind::kSequence, ItemOperandKind::kProperty,
                    ItemOperandKind::kTopLevelProperty}) {
    auto wrapped = ItemExpr::Wrap(&e, kind);
    EXPECT_TRUE(wrapped.Admits(ItemOperation::kNamedItemOfTypeOp));
  }
}

TEST(RewriteItem, UndefinedTypeAdmitsNothing) {
  Expr e{};
  auto wrapped = ItemExpr::Wrap(&e, ItemOperandKind::kUndefinedType);
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kNamedItemOfTypeOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kSequenceInstanceOp));
  EXPECT_FALSE(wrapped.Admits(ItemOperation::kPropertyInstanceOp));
}

}  // namespace
