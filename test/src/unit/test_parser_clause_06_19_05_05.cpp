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

TEST(EnumMethods, NumCallAsStatementParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {A, B} ab_e;\n"
              "  ab_e e;\n"
              "  initial e.num();\n"
              "endmodule\n"));
}

TEST(EnumMethods, NumCallInConditionalParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {X, Y, Z} xyz_e;\n"
              "  xyz_e v;\n"
              "  int n;\n"
              "  initial begin\n"
              "    if (v.num() > 0) n = 1;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
