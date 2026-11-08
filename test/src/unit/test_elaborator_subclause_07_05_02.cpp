#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DynamicArraySizeValidation, SizeCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int s;\n"
             "  initial s = d.size();\n"
             "endmodule\n"));
}

}  // namespace
