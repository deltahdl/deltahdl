#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_class.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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
                            "external constraint block 'C::proto2' comes "
                            "before the declaration of class 'C' ends",
                            1, "18.5.1"));
}

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
                            "external constraint block 'C::proto2' comes "
                            "before the declaration of class 'C' ends",
                            2, "18.5.1"));
}

TEST(ExternalConstraintBlocks, BlockForUndeclaredClassRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("constraint D::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "external constraint block 'D::c' has no class 'D' "
                            "declared in its own scope",
                            1, "18.5.1"));
}

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
                            "external constraint block 'D::c' has no class 'D' "
                            "declared in its own scope",
                            8, "18.5.1"));
}

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
                            "external constraint block 'C::p' comes before the "
                            "declaration of class 'C' ends",
                            2, "18.5.1"));
}

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
                            "external constraint block 'C::p' has no class 'C' "
                            "declared in its own scope",
                            6, "18.5.1"));
}

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

TEST(ExternalConstraintBlocks, ExplicitPrototypeInGenerateClassNeedsBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  if (0) begin : a\n"
             "  end else begin : b\n"
             "    class C;\n"
             "      rand int x;\n"
             "      extern constraint p;\n"
             "    endclass\n"
             "  end\n"
             "  for (genvar i = 0; i < 1; i++) begin : l\n"
             "    class D;\n"
             "      rand int y;\n"
             "      extern constraint q;\n"
             "    endclass\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      class E;\n"
             "        rand int z;\n"
             "        extern constraint r;\n"
             "      endclass\n"
             "    end\n"
             "  endcase\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'p' in class 'C' "
                            "has no external constraint block",
                            6, "18.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'q' in class 'D' "
                            "has no external constraint block",
                            12, "18.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'r' in class 'E' "
                            "has no external constraint block",
                            19, "18.5.1"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint block name 'proto1' is not unique within class 'C'", 4,
      "18.5"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constraint block name 'proto2' is not unique within class 'C'", 4,
      "18.5"));
}

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
  EXPECT_EQ(proto->constraint_exprs.size(), 1u);
}

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
