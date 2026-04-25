#include "fixture_elaborator.h"

namespace {

// §33.5.1: after compiling all cells on the command line into the
// library, the tool locates the top-level cell and descends the
// hierarchy, binding each instance as it is encountered.  A library
// cell that no instance ever references is therefore not part of the
// elaborated design even though the parser placed it in the library.
TEST(SinglePassDescend, UnusedLibraryCellAbsentFromDesign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module unused;\n"
      "endmodule\n"
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("child"));
  EXPECT_FALSE(design->all_modules.contains("unused"));
}

// Descent is transitive: top instantiates mid, mid instantiates leaf.
// The hierarchy walk reaches every instance, so all three modules
// appear in the elaborated design.  This exercises the recursive
// binding step §33.5.1 calls out ("proceed down the hierarchy,
// binding each instance as it is encountered").
TEST(SinglePassDescend, TransitiveHierarchyFullyBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

// Descent treats sibling subtrees independently: a chain reachable
// only through an unused cell stays out of the design.  Here `dead`
// instantiates `dead_leaf`, but nothing instantiates `dead`, so the
// whole subtree sits in the library and never reaches the elaborated
// hierarchy rooted at `top`.
TEST(SinglePassDescend, UnreachableSubtreeStaysInLibrary) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dead_leaf;\n"
      "endmodule\n"
      "module dead;\n"
      "  dead_leaf dl();\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 1u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_FALSE(design->all_modules.contains("dead"));
  EXPECT_FALSE(design->all_modules.contains("dead_leaf"));
}

// Choosing a different top out of the same library yields a different
// elaborated design.  Both candidate tops were "compiled into the
// library" at parse time, so either one can serve as the root of the
// hierarchy walk; the descent step decides what ends up bound.
TEST(SinglePassDescend, AlternateTopProducesAlternateDesign) {
  ElabFixture f1;
  auto* d1 = ElaborateSrc(
      "module helper;\n"
      "endmodule\n"
      "module rootA;\n"
      "  helper h();\n"
      "endmodule\n"
      "module rootB;\n"
      "endmodule\n",
      f1, "rootA");
  ASSERT_FALSE(f1.has_errors);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(d1->top_modules[0]->name, "rootA");
  EXPECT_TRUE(d1->all_modules.contains("helper"));
  EXPECT_FALSE(d1->all_modules.contains("rootB"));

  ElabFixture f2;
  auto* d2 = ElaborateSrc(
      "module helper;\n"
      "endmodule\n"
      "module rootA;\n"
      "  helper h();\n"
      "endmodule\n"
      "module rootB;\n"
      "endmodule\n",
      f2, "rootB");
  ASSERT_FALSE(f2.has_errors);
  ASSERT_NE(d2, nullptr);
  EXPECT_EQ(d2->top_modules[0]->name, "rootB");
  EXPECT_FALSE(d2->all_modules.contains("helper"));
  EXPECT_FALSE(d2->all_modules.contains("rootA"));
}

// Error path: when the descent encounters an instance whose target is
// not in the library (no source description for it was provided on
// the command line), elaboration fails.  This is the consequence of
// §33.5.1's rule that "only these source descriptions can be used to
// bind cell instances in the current design": there is no fallback
// pool to draw missing cells from.
TEST(SinglePassDescend, InstanceWithNoLibraryEntryFails) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  not_in_library u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
