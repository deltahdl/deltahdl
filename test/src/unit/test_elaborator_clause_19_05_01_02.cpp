#include <gtest/gtest.h>

#include "elaborator/coverpoint_bin_set_expression.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §19.5.1.2: a set_covergroup_expression may yield any array whose element type
// is assignment compatible with the coverpoint type. An integral element type
// is assignment compatible with an integral coverpoint.
TEST(CoverpointBinSetExpression, ElementTypeAssignmentCompatibleIsAllowed) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kByte;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: an element type that is not assignment compatible with the
// coverpoint type is rejected. A string element type cannot be assigned to an
// integral coverpoint.
TEST(CoverpointBinSetExpression, IncompatibleElementTypeIsRejected) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: the coverpoint type is not restricted to integral -- a coverpoint
// may be a real type (§19.5), and a real element type is assignment compatible
// with a real coverpoint, so a set expression yielding a real array is allowed.
TEST(CoverpointBinSetExpression, RealCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: an element type that is not assignment compatible with a real
// coverpoint is still rejected -- a string element cannot be assigned to a real
// coverpoint, exercising the reject path in the real coverpoint domain.
TEST(CoverpointBinSetExpression, RealCoverpointRejectsStringElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: assignment compatibility spans the integral/real boundary, so a
// real coverpoint admits an integral element type -- the integral values are
// assignment compatible with the real coverpoint. This exercises the
// cross-domain assignment-compatibility path, distinct from the same-domain
// integral and real cases above.
TEST(CoverpointBinSetExpression, RealCoverpointAcceptsIntegralElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kInt;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: the cross-domain path holds in the other direction as well -- an
// integral coverpoint admits a real element type, since a real value is
// assignment compatible with an integral coverpoint.
TEST(CoverpointBinSetExpression, IntegralCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: every array kind (fixed-size, dynamic, queue) is permitted.
TEST(CoverpointBinSetExpression, NonAssociativeArrayKindsAreAllowed) {
  EXPECT_TRUE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kFixedSize));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kDynamic));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kQueue));
}

// §19.5.1.2: associative arrays are the one exception that is not permitted.
TEST(CoverpointBinSetExpression, AssociativeArrayKindIsRejected) {
  EXPECT_FALSE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kAssociative));
}

// §19.5.1.2: identifiers declared within the covergroup (coverpoint identifiers
// and bin identifiers) are not visible within the expression.
TEST(CoverpointBinSetExpression, CovergroupLocalNamesAreNotVisible) {
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kCoverpointIdentifier));
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kBinIdentifier));
}

// §19.5.1.2: a name declared outside the covergroup remains visible.
TEST(CoverpointBinSetExpression, ExternalNameIsVisible) {
  EXPECT_TRUE(SetExpressionNameVisible(SetExpressionNameOrigin::kExternal));
}

}  // namespace
