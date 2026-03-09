#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA817, SuperNewFirstStatementOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new();\n"
             "    super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ElabA817, SuperNewNotFirstStatementError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    x = 1;\n"
             "    super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ElabA817, ExtendsArgsAndSuperNewError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base(5);\n"
             "  function new();\n"
             "    super.new(5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ElabA817, ExtendsArgsNoSuperNewOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class EtherPacket extends Base(5);\n"
             "endclass\n"
             "module m;\n"
             "  EtherPacket p;\n"
             "endmodule\n"));
}

TEST(ElabA817, ImplicitChainingOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

}  // namespace
