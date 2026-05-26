#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.2: ':initial' declares that a constraint is not an override, so a
// same-named constraint in a base class makes the ':initial' illegal.
TEST(ConstraintInheritance, InitialOverridingBaseRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':initial' applied to a constraint that has no same-named base class
// constraint is legal: it simply asserts the constraint is new.
TEST(ConstraintInheritance, InitialOnFreshConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':extends' declares that a constraint overrides one in a base class,
// so it is an error when no such base class constraint exists.
TEST(ConstraintInheritance, ExtendsWithoutBaseRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':extends' applied to a constraint that does replace a same-named
// base class constraint is legal.
TEST(ConstraintInheritance, ExtendsOverridingBaseAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':final' forbids any further subclass from replacing a constraint,
// so a subclass that declares a same-named constraint is in error.
TEST(ConstraintInheritance, ReplacingFinalBaseRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint :final c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':final' may be combined with ':extends'; overriding a non-final
// base class constraint and sealing it against further replacement is legal.
TEST(ConstraintInheritance, ExtendsFinalOverridingAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :extends :final c { x < 5; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: a pure constraint represents an obligation and shall not be declared
// in a non-abstract (non-virtual) class.
TEST(ConstraintInheritance, PureConstraintInNonAbstractRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: an abstract (virtual) class may declare pure constraints.
TEST(ConstraintInheritance, PureConstraintInAbstractAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: it is an error for a non-abstract class to leave a pure constraint
// inherited from an abstract base class without an implementation.
TEST(ConstraintInheritance, NonAbstractMissingPureImplRejected) {
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: a non-abstract class discharges an inherited pure constraint by
// providing a constraint block of the same name.
TEST(ConstraintInheritance, NonAbstractImplementsPureAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: an abstract class that inherits a constraint may replace it with a
// pure constraint of the same name, re-imposing the obligation on subclasses.
TEST(ConstraintInheritance, AbstractPureReplacesInheritedAccepted) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "virtual class D extends B;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: an abstract intermediate class need not implement an inherited pure
// constraint; the obligation propagates to its first non-abstract subclass.
TEST(ConstraintInheritance, AbstractIntermediateDefersPureObligation) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "virtual class M2 extends B;\n"
             "endclass\n"
             "class D extends M2;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: once a non-abstract class supplies a constraint that overrides an
// inherited pure constraint, that constraint is non-pure for every class
// derived from it, so a further subclass need not re-implement it.
TEST(ConstraintInheritance, OverriddenPureNotRequiredInFurtherSubclass) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class E extends D;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':final' seals a constraint against replacement, but a subclass that
// merely inherits the constraint without redeclaring it is unaffected.
TEST(ConstraintInheritance, FinalBaseInheritedWithoutReplacementAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint :final c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint d { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: ':final' may be combined with ':initial'. On a constraint that has
// no same-named base constraint, the combination is legal.
TEST(ConstraintInheritance, InitialFinalOnFreshConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  constraint :initial :final c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: when a constraint is split into a prototype and an external block,
// an override specifier on one but not the other is an error.
TEST(ConstraintInheritance, PrototypeAndExternalSpecifierMismatchRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :final c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: the same override specifier on both the prototype and the external
// block satisfies the parity requirement.
TEST(ConstraintInheritance, PrototypeAndExternalSpecifierMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :final c;\n"
             "endclass\n"
             "constraint :final C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.2: a class that declares a pure constraint shall not also complete a
// constraint of the same name through an external constraint block.
TEST(ConstraintInheritance, PureConstraintWithExternalBlockRejected) {
  EXPECT_FALSE(
      ElabOk("virtual class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

}
