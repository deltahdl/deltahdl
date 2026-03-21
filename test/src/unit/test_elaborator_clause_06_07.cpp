#include <gtest/gtest.h>

#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, VectoredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, VectoredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, BasicWireDeclOk) {
  NetDeclInfo info;
  info.type = NetType::kWire;
  EXPECT_TRUE(ValidateNetDecl(info));
}

}  // namespace
