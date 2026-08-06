#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.10: a constraint block may be qualified 'static' on its own. With no
// dynamic override specifier present, the declaration is legal.
TEST(StaticConstraint, PlainStaticConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10 (footnote 11): it is illegal to use a dynamic override specifier with
// a static constraint, so 'static' combined with ':initial' is an error.
TEST(StaticConstraint, StaticWithInitialRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10 (footnote 11): 'static' combined with ':extends' is likewise illegal,
// even when a same-named base constraint exists to satisfy ':extends' itself.
TEST(StaticConstraint, StaticWithExtendsRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  static constraint :extends c { x < 10; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10 (footnote 11): 'static' combined with ':final' is illegal.
TEST(StaticConstraint, StaticWithFinalRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint :final c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: the 'static' keyword shall appear on both a constraint prototype and
// its completing external block, or on neither. A static prototype with a
// non-static external block is an error.
TEST(StaticConstraint, StaticPrototypeNonStaticExternalRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: the mismatch is equally an error the other way around — a non-static
// prototype completed by a static external block.
TEST(StaticConstraint, NonStaticPrototypeStaticExternalRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "static constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: 'static' on both the prototype and the external block satisfies the
// matching requirement.
TEST(StaticConstraint, StaticPrototypeAndExternalAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c;\n"
             "endclass\n"
             "static constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: 'static' absent from both the prototype and the external block also
// satisfies the matching requirement (absence on both is allowed).
TEST(StaticConstraint, NonStaticPrototypeAndExternalAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: a pure constraint may be qualified 'static', and an overriding
// constraint must match. A static pure constraint overridden by a static
// constraint is legal.
TEST(StaticConstraint, StaticPureOverriddenByStaticAccepted) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  static pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: an overriding constraint that does not match the static
// qualification of the pure constraint it overrides is an error — a static pure
// constraint overridden by a non-static constraint.
TEST(StaticConstraint, StaticPureOverriddenByNonStaticRejected) {
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  static pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: the mismatch is symmetric — a non-static pure constraint overridden
// by a static constraint is also an error.
TEST(StaticConstraint, NonStaticPureOverriddenByStaticRejected) {
  EXPECT_FALSE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "class D extends B;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.10: when neither the pure constraint nor its override is static, the
// qualifications match (both absent), so the override is legal — the static
// parity check must not flag the ordinary non-static override.
TEST(StaticConstraint, NonStaticPureOverriddenByNonStaticAccepted) {
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

}  // namespace
