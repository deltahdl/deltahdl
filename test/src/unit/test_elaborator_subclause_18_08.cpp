#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.8: the rand_mode() method is built-in and cannot be overridden, so a class
// that declares a method of that name is illegal.
TEST(RandModeBuiltin, OverrideRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void rand_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.8: the override prohibition is by method name, independent of signature.
// Declaring rand_mode with the nonvoid (int, no-argument) query signature is
// just as illegal as the void form.
TEST(RandModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int rand_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// A class that defines an ordinary method and leaves rand_mode alone elaborates
// cleanly.
TEST(RandModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.8: a compiler error shall be issued if the variable named in a rand_mode()
// call does not exist within the object's class hierarchy.
TEST(RandModeNamedVariable, MissingVariableRejected) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: a compiler error shall be issued if the named variable exists but is
// not declared rand or randc. A plain (non-random) data member cannot be the
// subject of rand_mode().
TEST(RandModeNamedVariable, NonRandVariableRejected) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.y.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// Naming a variable that is declared rand elaborates without error.
TEST(RandModeNamedVariable, RandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: a randc variable is a random variable too, so naming one in rand_mode()
// is legal.
TEST(RandModeNamedVariable, RandcVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  randc bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: the specified variable may be inherited from a base class -- it need
// only exist somewhere in the class hierarchy. Naming a base-class rand
// variable through a derived handle is legal.
TEST(RandModeNamedVariable, InheritedRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: the no-name void form applies to every random variable in the object
// and names nothing to validate, so it elaborates cleanly.
TEST(RandModeNamedVariable, UnnamedFormAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.8: omitting the variable name is only allowed when rand_mode() is called
// as a void function -- i.e. with an on/off argument. A no-name call that also
// passes no argument is neither the void all-variables form nor the nonvoid
// query form (which must name a variable), so it is illegal.
TEST(RandModeNamedVariable, UnnamedQueryWithoutArgumentRejected) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
