#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(EnumMethods, NameCallParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {RED, GREEN, BLUE} color_e;\n"
              "  color_e c;\n"
              "  string s;\n"
              "  initial s = c.name();\n"
              "endmodule\n"));
}

TEST(EnumMethods, NameCallAsStatementParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {A, B} ab_e;\n"
              "  ab_e e;\n"
              "  initial e.name();\n"
              "endmodule\n"));
}

TEST(EnumMethods, NameCallInConditionalParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {X, Y, Z} xyz_e;\n"
              "  xyz_e v;\n"
              "  string s;\n"
              "  initial begin\n"
              "    if (v.name() != \"\") s = v.name();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
