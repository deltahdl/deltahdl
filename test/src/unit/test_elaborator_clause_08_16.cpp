#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA816, SubclassToSuperclassAssignOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
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

TEST(ElabA816, CastSuperToSubclassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "endclass\n"
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

TEST(ElabA816, CastAsFunctionOk) {
  EXPECT_TRUE(
      ElabOk("class Base; int x; endclass\n"
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

TEST(ElabA816, CastWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Derived extends Base; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    $cast(d, null);\n"
             "  end\n"
             "endmodule\n"));
}

}
