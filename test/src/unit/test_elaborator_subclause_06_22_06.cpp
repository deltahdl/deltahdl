#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MatchingNettypes, SameNettypeTerminalsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic nt;\n"
      "  nt a;\n"
      "  nt b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MatchingNettypes, AliasAndRenamedNettypeTerminalsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t alias_t;\n"
      "  base_t a;\n"
      "  alias_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MatchingNettypes, DistinctNettypeTerminalsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic foo_t;\n"
      "  nettype logic bar_t;\n"
      "  foo_t a;\n"
      "  bar_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot connect different user-defined nettypes "
                            "('foo_t' and 'bar_t')",
                            6, "28.8"));
}

TEST(MatchingNettypes, AliasOfAliasMatchesBaseNettype) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t mid_t;\n"
      "  nettype mid_t leaf_t;\n"
      "  base_t a;\n"
      "  leaf_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MatchingNettypes, SiblingAliasesOfSameNettypeMatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t left_t;\n"
      "  nettype base_t right_t;\n"
      "  left_t a;\n"
      "  right_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(MatchingNettypes, NettypesDeclaredOverOneTypedefDoNotMatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef logic T;\n"
      "  nettype T foo_t;\n"
      "  nettype T bar_t;\n"
      "  foo_t a;\n"
      "  bar_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot connect different user-defined nettypes "
                            "('foo_t' and 'bar_t')",
                            7, "28.8"));
}

}  // namespace
