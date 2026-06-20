#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.1: the implicit prototype form ('constraint name;') with no external
// block is treated as an empty constraint, which is legal.
TEST(ExternalConstraintBlocks, ImplicitPrototypeWithoutBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: the explicit prototype form ('extern constraint name;') shall have a
// corresponding external constraint block; absent one it is an error.
TEST(ExternalConstraintBlocks, ExplicitPrototypeWithoutBlockRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: an explicit prototype completed by exactly one external constraint
// block is legal.
TEST(ExternalConstraintBlocks, ExplicitPrototypeWithBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "constraint C::proto2 { x >= 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: an implicit prototype may also be completed by an external block.
TEST(ExternalConstraintBlocks, ImplicitPrototypeWithBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "endclass\n"
             "constraint C::proto1 { x inside {-4, 5, 7}; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: it is an error if more than one external constraint block is provided
// for a given prototype.
TEST(ExternalConstraintBlocks, MultipleBlocksForPrototypeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "constraint C::proto2 { x >= 0; }\n"
             "constraint C::proto2 { x < 10; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: an external constraint block shall appear after the declaration of
// its class; a block placed before the class is an error.
TEST(ExternalConstraintBlocks, BlockBeforeClassRejected) {
  EXPECT_FALSE(
      ElabOk("constraint C::proto2 { x >= 0; }\n"
             "class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: a constraint block of the same name as a prototype in the same class
// declaration is an error.
TEST(ExternalConstraintBlocks, BlockSameNameAsPrototypeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "  constraint proto1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: the "more than one external block" error applies to either prototype
// form, so the implicit form with two completing blocks is also an error.
TEST(ExternalConstraintBlocks, MultipleBlocksForImplicitPrototypeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "endclass\n"
             "constraint C::proto1 { x > 0; }\n"
             "constraint C::proto1 { x < 10; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: completion is matched per class, so the same prototype name in two
// different classes, each completed by its own scope-resolved block, is legal.
TEST(ExternalConstraintBlocks, SameNamePrototypeInDistinctClassesAccepted) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "  rand int x;\n"
             "  extern constraint p;\n"
             "endclass\n"
             "class B;\n"
             "  rand int y;\n"
             "  extern constraint p;\n"
             "endclass\n"
             "constraint A::p { x > 0; }\n"
             "constraint B::p { y > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: a class may carry several prototypes, each completed by its own
// external constraint block.
TEST(ExternalConstraintBlocks,
     MultipleDistinctPrototypesEachCompletedAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x, y;\n"
             "  extern constraint lo;\n"
             "  extern constraint hi;\n"
             "endclass\n"
             "constraint C::lo { x > 0; }\n"
             "constraint C::hi { y < 10; }\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.1: completion is matched per class. An external block that completes a
// same-named prototype in a different class does not satisfy this class's
// explicit prototype, so the unmatched explicit prototype is still an error.
// Here only B::p is provided, leaving A's explicit prototype 'p' without a
// block despite a constraint of the same name existing for B.
TEST(ExternalConstraintBlocks, ExplicitPrototypeNotSatisfiedByOtherClassBlock) {
  EXPECT_FALSE(
      ElabOk("class A;\n"
             "  rand int x;\n"
             "  extern constraint p;\n"
             "endclass\n"
             "class B;\n"
             "  rand int y;\n"
             "  extern constraint p;\n"
             "endclass\n"
             "constraint B::p { y > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
