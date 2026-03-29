#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DataHidingElaboration, PublicMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
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

TEST(DataHidingElaboration, LocalMemberAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
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

TEST(DataHidingElaboration, ProtectedMemberAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
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

TEST(DataHidingElaboration, LocalMethodAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
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

TEST(DataHidingElaboration, PublicMethodAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
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

TEST(DataHidingElaboration, ProtectedMethodAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  protected function void secret(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.secret();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalPropertyAccessInAlwaysBlockError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  always @(*) begin\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedPropertyAccessInAlwaysBlockError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  always @(*) begin\n"
             "    p.hidden = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorLocalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorProtectedAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
