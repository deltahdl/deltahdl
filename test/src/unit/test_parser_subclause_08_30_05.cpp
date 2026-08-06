#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakRefGetIdStaticCallParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj o;\n"
              "    longint id;\n"
              "    o = new();\n"
              "    id = weak_reference#(obj)::get_id(o);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefGetIdWithNullParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    longint id;\n"
              "    id = weak_reference#(obj)::get_id(null);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefGetIdInExpressionParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj o;\n"
              "    o = new();\n"
              "    if (weak_reference#(obj)::get_id(o) != 0)\n"
              "      $display(\"has id\");\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
