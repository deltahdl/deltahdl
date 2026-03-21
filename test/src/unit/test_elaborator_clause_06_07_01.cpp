#include <gtest/gtest.h>

#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, ValidNetDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::k4StateIntegral));
}

TEST(NetDecl, ValidNetDataTypeFixedUnpacked) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::kFixedUnpackedValid));
}

TEST(NetDecl, InvalidNetDataType2StateIntegral) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::k2StateIntegral));
}

TEST(NetDecl, InvalidNetDataTypeReal) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kReal));
}

TEST(NetDecl, InvalidNetDataTypeDynamicArray) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kDynamicArray));
}

TEST(NetDecl, InvalidNetDataTypeString) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kString));
}

}  // namespace
