#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstructorElaboration, ExplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer command;\n"
             "  function new();\n"
             "    command = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "  function new(int cmd, int addr);\n"
             "    command = cmd;\n"
             "    address = addr;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new(1, 2);\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithDefaultArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  bit [12:0] address;\n"
             "  int cmd_time;\n"
             "  function new(int cmd = 0, bit [12:0] adrs = 0, int t = 0);\n"
             "    command = cmd;\n"
             "    address = adrs;\n"
             "    cmd_time = t;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorDerivedElaborates) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, PropertyWithExplicitDefaultElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x = 5;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, LocalConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  local function new();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ProtectedConstructorAccessibleToSubclass) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int b;\n"
             "  protected function new();\n"
             "    b = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int c;\n"
             "  function new();\n"
             "    super.new();\n"
             "    c = 2;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child ch;\n"
             "  initial ch = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithTimingControlError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "    #5 x = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
}

TEST(ClassConstructorElaboration, ConstructorWithEventControlError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  int y;\n"
      "  function new();\n"
      "    @(y) x = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 5,
      "13.4"));
}

}  // namespace
