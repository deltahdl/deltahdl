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

// §8.7: a constructor may be declared as a local method. The qualifier is
// accepted (unlike static/virtual, which are rejected) and the class still
// elaborates. Access control on the local `new` is §8.18 machinery.
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

// §8.7: a constructor may be declared as a protected method. A protected
// constructor is reachable from a subclass, so the derived class's super.new()
// call elaborates cleanly against it.
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

// §8.7 states "The new operation is defined as a function with no return type,
// and like any other function, it shall be nonblocking", which defers the
// nonblocking requirement to the rule §13.4 states for every function. The
// report therefore names §13.4.
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

// §8.7's nonblocking requirement bars every kind of time control in the
// constructor, not just delays. An event control is rejected under the same
// §13.4 rule, since §8.7 states the requirement only by reference to what holds
// for any other function.
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
