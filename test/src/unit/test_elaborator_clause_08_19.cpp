#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConstantClassPropertyElaboration, GlobalConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Jumbo_Packet;\n"
             "  const int max_size = 9 * 1024;\n"
             "endclass\n"
             "module m;\n"
             "  Jumbo_Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, StaticConstGlobalOk) {
  EXPECT_TRUE(
      ElabOk("class Config;\n"
             "  static const int VERSION = 3;\n"
             "endclass\n"
             "module m;\n"
             "  Config c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Big_Packet;\n"
             "  const int size;\n"
             "  function new();\n"
             "    size = 4096;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Big_Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstStaticError) {
  EXPECT_FALSE(
      ElabOk("class Bad;\n"
             "  static const int size;\n"
             "endclass\n"
             "module m;\n"
             "  Bad b;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, GlobalAndInstanceConstInSameClass) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  const int max_size = 1024;\n"
             "  const int size;\n"
             "  function new();\n"
             "    size = 512;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, MultipleInstanceConstantsOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  const int a;\n"
             "  const int b;\n"
             "  function new(int x, int y);\n"
             "    a = x;\n"
             "    b = y;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstStaticErrorWithInit) {
  // static + no init_expr = instance constant + static → error.
  // Having an init_expr makes it a global constant, so static is fine.
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static const int X = 42;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, ConstWithLocalQualifierOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local const int X = 10;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, ConstWithProtectedQualifierOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected const int Y = 20;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstInSubclass) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  const int id;\n"
             "  function new(int i);\n"
             "    id = i;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function new();\n"
             "    super.new(99);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInConstructorError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  const int MAX = 100;\n"
             "  function new();\n"
             "    MAX = 200;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInMethodError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  const int MAX = 100;\n"
             "  function void reset();\n"
             "    MAX = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignInMethodError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  const int id;\n"
             "  function new();\n"
             "    id = 1;\n"
             "  endfunction\n"
             "  function void reset();\n"
             "    id = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignInTaskError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  const int id;\n"
             "  function new();\n"
             "    id = 1;\n"
             "  endfunction\n"
             "  task set_id();\n"
             "    id = 2;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
