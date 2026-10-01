#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_class.h"
#include "parser/parser.h"

using namespace delta;

namespace {

// 18.5.1: the explicit prototype form ('extern constraint name;') shall have a
// corresponding external constraint block; absent one it is an error.
TEST(ExternalConstraintBlocks, ExplicitPrototypeWithoutBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit constraint prototype 'proto2' in class 'C' has no external "
      "constraint block",
      3, "18.5.1"));
}

// 18.5.1: it is an error if more than one external constraint block is provided
// for a given prototype.
TEST(ExternalConstraintBlocks, MultipleBlocksForPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "constraint C::proto2 { x >= 0; }\n"
             "constraint C::proto2 { x < 10; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint prototype 'proto2' in class 'C' is "
                            "completed by more than one external constraint "
                            "block",
                            3, "18.5.1"));
}

// 18.5.1: an external constraint block shall appear after the declaration of
// its class; a block placed before the class is an error.
TEST(ExternalConstraintBlocks, BlockBeforeClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("constraint C::proto2 { x >= 0; }\n"
             "class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::proto2' shall "
                            "appear after the declaration of class 'C'",
                            1, "18.5.1"));
}

// 18.5.1: the block shall follow its class in the scope that declares both,
// a package included, so a block placed ahead of its class inside a package is
// an error there too.
TEST(ExternalConstraintBlocks, BlockBeforeClassInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  constraint C::proto2 { x >= 0; }\n"
             "  class C;\n"
             "    rand int x;\n"
             "    extern constraint proto2;\n"
             "  endclass\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::proto2' shall "
                            "appear after the declaration of class 'C'",
                            2, "18.5.1"));
}

// 18.5.1: the block shall appear in the scope of its class declaration, so a
// block naming a class that its scope never declares is an error.
TEST(ExternalConstraintBlocks, BlockForUndeclaredClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("constraint D::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'D::c' shall appear in "
                            "the scope that declares class 'D'",
                            1, "18.5.1"));
}

// 18.5.1: a block in one package does not complete a class another package
// declares; the package holding the block declares no such class.
TEST(ExternalConstraintBlocks, BlockForOtherPackagesClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package other;\n"
             "  class D;\n"
             "    rand int x;\n"
             "    constraint c;\n"
             "  endclass\n"
             "endpackage\n"
             "package pkg;\n"
             "  constraint D::c { x > 0; }\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'D::c' shall appear in "
                            "the scope that declares class 'D'",
                            8, "18.5.1"));
}

// 18.5.1: inside a module the block shall follow its class there too.
TEST(ExternalConstraintBlocks, BlockBeforeClassInModuleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  constraint C::p { x > 0; }\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint p;\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::p' shall "
                            "appear after the declaration of class 'C'",
                            2, "18.5.1"));
}

// 18.5.1: a block in a module does not complete a class of the compilation
// unit; the module declares no class of that name.
TEST(ExternalConstraintBlocks, BlockInModuleForUnitClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint p;\n"
             "endclass\n"
             "module m;\n"
             "  constraint C::p { x > 0; }\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'C::p' shall appear in "
                            "the scope that declares class 'C'",
                            6, "18.5.1"));
}

// 18.5.1: an explicit prototype needs its block wherever its class stands, a
// class of a package or of a module as much as one of the compilation unit.
TEST(ExternalConstraintBlocks,
     ExplicitPrototypeInPackageOrModuleClassNeedsBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    extern constraint p;\n"
             "  endclass\n"
             "endpackage\n"
             "module m;\n"
             "  class D;\n"
             "    rand int y;\n"
             "    extern constraint q;\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'p' in class 'C' "
                            "has no external constraint block",
                            4, "18.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'q' in class 'D' "
                            "has no external constraint block",
                            10, "18.5.1"));
}

// 18.5.1: a block completes the class of its own scope only, so the block a
// package gives its C leaves the explicit prototype of the compilation unit's
// C without one.
TEST(ExternalConstraintBlocks, OtherScopesBlockDoesNotCompleteThePrototype) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint p;\n"
             "endclass\n"
             "package pkg;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    extern constraint p;\n"
             "  endclass\n"
             "  constraint C::p { x > 0; }\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'p' in class 'C' "
                            "has no external constraint block",
                            3, "18.5.1"));
}

// 18.5.1, 18.5.2 and 18.5.10: two classes named C in two scopes each take
// their own block, so neither prototype counts as completed twice, and the
// static qualifier of one pair is not held against the other's.
TEST(ExternalConstraintBlocks, SameNamedClassesInTwoScopesEachTakeTheirBlock) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint p;\n"
             "endclass\n"
             "static constraint C::p { x > 0; }\n"
             "package pkg;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint p;\n"
             "  endclass\n"
             "  constraint C::p { x < 0; }\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
}

// 18.5.2: a pure constraint conflicts with a block of its own class only, not
// with the block another scope gives a class of the same name.
TEST(ExternalConstraintBlocks, PureConstraintIgnoresOtherScopesBlock) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("virtual class C;\n"
             "  pure constraint p;\n"
             "endclass\n"
             "package pkg;\n"
             "  class C;\n"
             "    rand int x;\n"
             "    constraint p;\n"
             "  endclass\n"
             "  constraint C::p { x > 0; }\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
}

// 18.5.1: the completed prototype is the block's body, so the rules on what a
// constraint holds reach a block written outside the class; here 18.5.4's ban
// on a randc member of a unique group.
TEST(ExternalConstraintBlocks, BlockBodyIsCheckedLikeAnInClassBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  constraint p;\n"
             "endclass\n"
             "constraint C::p { unique {a, b}; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 6,
      "18.5.4"));
}

// 18.5.1: a constraint block of the same name as a prototype in the same class
// declaration is an error. Here the prototype is the implicit form.
TEST(ExternalConstraintBlocks, BlockSameNameAsPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "  constraint proto1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  // The rule that rejects this source is the constraint-name uniqueness rule of
  // 18.5, reported by ClassConstraintValidator::ValidateOneClassConstraintNames
  // in src/elaborator/elaborator_validate_class_constraints.cpp under
  // Subclause("18.5"), not one of the 18.5.1 completion reports.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint block name 'proto1' is not unique within class 'C'", 4,
      "18.5"));
}

// 18.5.1: the same-name-as-a-prototype rule holds for either prototype form, so
// an in-class block sharing the name of an explicit ('extern') prototype in the
// same class is likewise an error.
TEST(ExternalConstraintBlocks, BlockSameNameAsExplicitPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint proto2;\n"
             "  constraint proto2 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  // As in BlockSameNameAsPrototypeRejected, the same-name rule is reported
  // under Subclause("18.5"). The explicit prototype is separately reported
  // under 18.5.1 for having no external block, which is a different claim.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint block name 'proto2' is not unique within class 'C'", 4,
      "18.5"));
}

// 18.5.1: the "more than one external block" error applies to either prototype
// form, so the implicit form with two completing blocks is also an error.
TEST(ExternalConstraintBlocks, MultipleBlocksForImplicitPrototypeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint proto1;\n"
             "endclass\n"
             "constraint C::proto1 { x > 0; }\n"
             "constraint C::proto1 { x < 10; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint prototype 'proto1' in class 'C' is "
                            "completed by more than one external constraint "
                            "block",
                            3, "18.5.1"));
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
  ElabFixture f;
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
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit constraint prototype 'p' in class 'A' has no external "
      "constraint block",
      3, "18.5.1"));
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
