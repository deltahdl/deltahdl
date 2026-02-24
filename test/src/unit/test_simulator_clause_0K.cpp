// §K

#include <gtest/gtest.h>
#include "vpi/sv_vpi_user.h"

namespace {

TEST(SvVpiUser, ThreadCallbackReasons) {
  EXPECT_EQ(cbStartOfThread, 600);
  EXPECT_EQ(cbEndOfThread, 601);
  EXPECT_EQ(cbCreateObj, 700);
}

}  // namespace
