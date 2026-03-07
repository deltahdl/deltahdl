#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection8, DynamicCastClassHandles) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class Base;\n"
              "    int x;\n"
              "  endclass\n"
              "  class Derived extends Base;\n"
              "    int y;\n"
              "  endclass\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    $cast(d, b);\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: Subclass-to-superclass assignment is always legal.
TEST(ParserA816, SubclassToSuperclassAssign) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  int i;\n"
              "endclass\n"
              "class LinkedPacket extends Packet;\n"
              "  int j;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Packet p;\n"
              "    LinkedPacket lp;\n"
              "    lp = new;\n"
              "    p = lp;\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: $cast as function (returns int).
TEST(ParserA816, CastAsFunction) {
  EXPECT_TRUE(
      ParseOk("class Base; int x; endclass\n"
              "class Derived extends Base; int y; endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    int ok;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    ok = $cast(d, b);\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: $cast as task (no return value).
TEST(ParserA816, CastAsTask) {
  EXPECT_TRUE(
      ParseOk("class Base; int x; endclass\n"
              "class Derived extends Base; int y; endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    $cast(d, b);\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: $cast with null source.
TEST(ParserA816, CastWithNullSource) {
  EXPECT_TRUE(
      ParseOk("class Base; endclass\n"
              "class Derived extends Base; endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Derived d;\n"
              "    $cast(d, null);\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: Superclass-to-subclass direct assignment parses (elaborator catches).
TEST(ParserA816, SuperclassToSubclassAssignParses) {
  EXPECT_TRUE(
      ParseOk("class Base; int x; endclass\n"
              "class Derived extends Base; int y; endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    b = new;\n"
              "    d = b;\n"
              "  end\n"
              "endmodule\n"));
}

// §8.16: $cast in conditional expression.
TEST(ParserA816, CastInConditional) {
  EXPECT_TRUE(
      ParseOk("class Base; endclass\n"
              "class Derived extends Base; endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    if ($cast(d, b)) begin\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
