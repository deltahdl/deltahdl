// §6.9.2: Vector net accessibility

#include <gtest/gtest.h>

#include <cstdint>

#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, VectoredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

}  // namespace
