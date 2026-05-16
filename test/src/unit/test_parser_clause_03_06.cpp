// §3.6: The checker construct, enclosed by the keywords
// checker ... endchecker, represents a verification block encapsulating
// assertions along with the modeling code.

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Enclosure between checker / endchecker ---

TEST(CheckerBlockParsing, CheckerEndcheckerEnclosureProducesCheckerDecl) {
  auto r = Parse("checker c; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "c");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST(CheckerBlockParsing, CheckerBodyTerminatesOnlyAtEndchecker) {
  // Without the endchecker keyword the parser cannot close the checker block.
  auto r = Parse("checker c; initial begin end\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Verification block represented as a distinct top-level kind ---

TEST(CheckerBlockParsing, CheckerCollectedSeparatelyFromModule) {
  auto r = Parse(
      "module m; endmodule\n"
      "checker c; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
}

TEST(CheckerBlockParsing, CheckerKindDistinctFromProgramAndInterface) {
  auto r = Parse(
      "interface i; endinterface\n"
      "program p; endprogram\n"
      "checker c; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(CheckerBlockParsing, MultipleCheckerDeclarationsAllEnclosed) {
  auto r = Parse(
      "checker c1; endchecker\n"
      "checker c2; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->name, "c1");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_EQ(r.cu->checkers[1]->name, "c2");
  EXPECT_EQ(r.cu->checkers[1]->decl_kind, ModuleDeclKind::kChecker);
}

}  // namespace
