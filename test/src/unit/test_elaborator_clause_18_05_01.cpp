#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
// declaration is an error. Here the prototype is the implicit form.
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

// 18.5.1: the same-name-as-a-prototype rule holds for either prototype form, so
// an in-class block sharing the name of an explicit ('extern') prototype in the
// same class is likewise an error.
TEST(ExternalConstraintBlocks, BlockSameNameAsExplicitPrototypeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "  constraint proto2 { x > 0; }\n"
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

// Parse and elaborate 'src', then return the named constraint member of the
// named class from the elaborated compilation unit, or nullptr. Completion of
// external constraint blocks runs during elaboration, so the member returned
// reflects any relations attached by that completion.
const ClassMember* ElaborateAndFindConstraint(ElabFixture& f,
                                              const std::string& src,
                                              std::string_view cls_name,
                                              std::string_view cons_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("m");
  f.has_errors = f.diag.HasErrors();
  for (auto* cls : cu->classes) {
    if (cls->name != cls_name) continue;
    for (auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == cons_name) {
        return m;
      }
    }
  }
  return nullptr;
}

// 18.5.1: an external constraint block completes its prototype. After
// elaboration the prototype member carries the relations written in the
// external block, so at randomization the completed constraint restricts the
// variable rather than being ignored.
TEST(ExternalConstraintBlocks, ExternalBlockCompletesPrototypeRelations) {
  ElabFixture f;
  const ClassMember* proto =
      ElaborateAndFindConstraint(f,
                                 "class C;\n"
                                 "  rand int x;\n"
                                 "  extern constraint proto2;\n"
                                 "endclass\n"
                                 "constraint C::proto2 { x >= 0; }\n"
                                 "module m;\n"
                                 "endmodule\n",
                                 "C", "proto2");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(proto, nullptr);
  EXPECT_TRUE(proto->is_constraint_prototype);
  // Completion copies the external block's single relation onto the prototype,
  // which parsed with an empty body.
  EXPECT_EQ(proto->constraint_exprs.size(), 1u);
}

// 18.5.1: a prototype completed by a multi-relation external block receives
// every relation of that block.
TEST(ExternalConstraintBlocks,
     MultiRelationExternalBlockFullyCompletesPrototype) {
  ElabFixture f;
  const ClassMember* proto =
      ElaborateAndFindConstraint(f,
                                 "class C;\n"
                                 "  rand int x;\n"
                                 "  constraint proto1;\n"
                                 "endclass\n"
                                 "constraint C::proto1 { x >= 0; x < 10; }\n"
                                 "module m;\n"
                                 "endmodule\n",
                                 "C", "proto1");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(proto, nullptr);
  EXPECT_EQ(proto->constraint_exprs.size(), 2u);
}

// 18.5.1: an implicit prototype with no external constraint block is completed
// by nothing; its relation set stays empty, so it behaves as an empty
// constraint that has no effect on randomization (equivalent to constant 1).
TEST(ExternalConstraintBlocks, UncompletedImplicitPrototypeHasNoRelations) {
  ElabFixture f;
  const ClassMember* proto = ElaborateAndFindConstraint(f,
                                                        "class C;\n"
                                                        "  rand int x;\n"
                                                        "  constraint proto1;\n"
                                                        "endclass\n"
                                                        "module m;\n"
                                                        "endmodule\n",
                                                        "C", "proto1");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(proto, nullptr);
  EXPECT_TRUE(proto->is_constraint_prototype);
  EXPECT_TRUE(proto->constraint_exprs.empty());
}

}  // namespace
