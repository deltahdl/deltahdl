#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassCastParsing, SubclassToSuperclassAssign) {
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

TEST(ClassCastParsing, CastAsFunction) {
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

TEST(ClassCastParsing, CastAsTask) {
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

TEST(ClassCastParsing, CastWithNullSource) {
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

TEST(ClassCastParsing, SuperclassToSubclassAssignParses) {
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

TEST(ClassCastParsing, CastInConditional) {
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
