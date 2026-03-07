#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.18: Public member access from module scope is OK.
TEST(ElabA818, PublicMemberAccessOk) {
  EXPECT_TRUE(ElabOk(
      "class Packet;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.x = 1;\n"
      "  end\n"
      "endmodule\n"));
}

// §8.18: local member access from module scope is an error.
TEST(ElabA818, LocalMemberAccessError) {
  EXPECT_FALSE(ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "endmodule\n"));
}

// §8.18: protected member access from module scope is an error.
TEST(ElabA818, ProtectedMemberAccessError) {
  EXPECT_FALSE(ElabOk(
      "class Packet;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.hidden = 1;\n"
      "  end\n"
      "endmodule\n"));
}

// §8.18: local method access from module scope is an error.
TEST(ElabA818, LocalMethodAccessError) {
  EXPECT_FALSE(ElabOk(
      "class Packet;\n"
      "  local function int get_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.get_id();\n"
      "  end\n"
      "endmodule\n"));
}

// §8.18: Unqualified (public) method access is OK.
TEST(ElabA818, PublicMethodAccessOk) {
  EXPECT_TRUE(ElabOk(
      "class Packet;\n"
      "  function void show(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.show();\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
