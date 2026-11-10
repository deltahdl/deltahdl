#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

constexpr std::string_view kPortMismatch =
    "both sides shall be the same nettype";

TEST(MatchingNettypes, MatchingNettypesConnectAcrossPortsTranAndAlias) {
  for (std::string_view src : {
           "package pk; nettype logic nt; nettype nt nt2; endpackage\n"
           "module c(inout pk::nt p); endmodule\n"
           "module t; import pk::*; nt w; c u(w); endmodule\n",
           "package pk; nettype logic nt; nettype nt nt2; endpackage\n"
           "module c(inout pk::nt p); endmodule\n"
           "module t; import pk::*; nt2 w; c u(w); endmodule\n",
           "nettype logic nt;\n"
           "module c(inout nt p); endmodule\n"
           "module t; nt w; c u(w); endmodule\n",
           "nettype logic n1; nettype n1 n2;\n"
           "module c(inout n1 p); endmodule\n"
           "module t; n2 w; c u(w); endmodule\n",
           "package pk; nettype logic nt; endpackage\n"
           "module t; import pk::nt; nettype nt n2; nt a; n2 b; tran sw(a, "
           "b);\n"
           "endmodule\n",
           "module t; nettype logic nt; nettype nt n2; nt a; n2 b; alias a = "
           "b;\n"
           "endmodule\n",
       }) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(std::string(src), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

TEST(MatchingNettypes, DistinctNettypesAcrossAPortAreReported) {
  for (std::string_view src : {
           "nettype logic n1; nettype logic n2;\n"
           "module c(inout n1 p); endmodule\n"
           "module t; n2 w; c u(w); endmodule\n",
           "package pk; nettype logic n1; nettype logic n3; endpackage\n"
           "module c(inout pk::n1 p); endmodule\n"
           "module t; pk::n3 w; c u(w); endmodule\n",
           "nettype logic n1; nettype logic n3;\n"
           "interface c(inout n1 p); endinterface\n"
           "module t; n3 w; c u(w); endmodule\n",
           "module c(p); nettype logic nc; inout nc p; endmodule\n"
           "module t; nettype logic nt; nt w; c u(w); endmodule\n",
       }) {
    std::string text(src);
    SCOPED_TRACE(text);
    ElabFixture f;
    ElaborateSrc(text, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(kPortMismatch),
                              LineHolding(text, "u(w)"), "23.3.3"));
  }
}

TEST(MatchingNettypes, DISABLED_SameNamedNettypesOfTwoModulesDoNotMatch) {
  std::string src =
      "module c(p); nettype logic nt; inout nt p; endmodule\n"
      "module t; nettype logic nt; nt w; c u(w); endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(kPortMismatch),
                            LineHolding(src, "u(w)"), "23.3.3"));
}

TEST(MatchingNettypes,
     DISABLED_TranBetweenDistinctNettypesInAGenerateBlockIsReported) {
  std::string src =
      "module t;\n"
      "  nettype logic n1;\n"
      "  nettype logic n3;\n"
      "  if (1) begin : g\n"
      "    n1 a;\n"
      "    n3 b;\n"
      "    tran sw(a, b);\n"
      "  end\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot connect different user-defined nettypes", 7,
                            "28.8"));
}

TEST(MatchingNettypes, DISABLED_AliasOfDistinctNettypesIsReported) {
  std::string src =
      "module t;\n"
      "  nettype logic n1;\n"
      "  nettype logic n3;\n"
      "  n1 a;\n"
      "  n3 b;\n"
      "  alias a = b;\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "different net types", 6, "10.11"));
}

TEST(MatchingNettypes,
     DISABLED_RealNettypeFromTheUnitOrAPackageMatchesAcrossAPort) {
  for (std::string_view src : {
           "function automatic real rs(input real d[]); return 0; endfunction\n"
           "nettype real nr with rs;\n"
           "module c(inout nr p); endmodule\n"
           "module t; nr w; c u(w); endmodule\n",
           "package pk;\n"
           "  function automatic real rs(input real d[]); return 0; "
           "endfunction\n"
           "  nettype real nr with rs;\n"
           "endpackage\n"
           "module c(inout pk::nr p); endmodule\n"
           "module t; import pk::*; nettype nr nr2; nr2 w; c u(w); endmodule\n",
       }) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(std::string(src), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
