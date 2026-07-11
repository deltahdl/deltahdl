#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.9: constraint_mode() is a built-in method and cannot be overridden, so a
// class that declares a method of that name is illegal.
TEST(ConstraintModeBuiltin, OverrideRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void constraint_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.9: the override prohibition is by method name, independent of signature.
// Declaring constraint_mode with the nonvoid (int, no-argument) query
// signature is just as illegal as the void form.
TEST(ConstraintModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function int constraint_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// A class that defines an ordinary method and leaves constraint_mode alone
// elaborates cleanly.
TEST(ConstraintModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.9: the constraint named in a constraint_mode() call shall exist in the
// object's class hierarchy. Naming a constraint block that does not exist is a
// compile-time error.
TEST(ConstraintModeNamedBlock, MissingConstraintRejected) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// Naming a constraint block that does exist on the object's class elaborates
// without error.
TEST(ConstraintModeNamedBlock, ExistingConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.filter1.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// A constraint block inherited from a base class counts as existing in the
// hierarchy, so naming it is legal.
TEST(ConstraintModeNamedBlock, InheritedConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.base_c.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: the existence check searches the whole class hierarchy, so a name that
// appears in neither the derived class nor any of its base classes is the
// error case. This exercises the multi-level walk returning "not found" across
// two levels, distinct from the single-class rejection.
TEST(ConstraintModeNamedBlock, MissingConstraintAcrossHierarchyRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.nonexistent.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: the no-name form applies to every constraint in the object and is
// allowed only as a void call. Because it names no constraint block, the
// existence check shall not fire: a call with no constraint identifier
// elaborates cleanly even though no block named "constraint_mode" exists.
TEST(ConstraintModeNamedBlock, UnnamedFormNotTreatedAsMissingBlock) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: omitting the constraint name is allowed only in the void form, which
// takes an on/off argument. A call that names no constraint and passes no
// argument is neither a legal void call nor a legal nonvoid query (the query
// form must name a block), so it is rejected.
TEST(ConstraintModeNamedBlock, UnnamedNoArgQueryRejected) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.constraint_mode();\n"
             "  end\n"
             "endmodule\n"));
}

// 18.9: the nonvoid query form is legal when it names a constraint block. This
// guards the no-name/no-argument rejection above from over-firing: a named,
// argument-less constraint_mode() query still elaborates cleanly.
TEST(ConstraintModeNamedBlock, NamedNoArgQueryAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.filter1.constraint_mode();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
