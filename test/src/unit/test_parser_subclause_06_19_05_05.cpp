#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(EnumMethods, NumCallParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {RED, GREEN, BLUE} color_e;\n"
              "  color_e c;\n"
              "  int n;\n"
              "  initial n = c.num();\n"
              "endmodule\n"));
}

}  // namespace
