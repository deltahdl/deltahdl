#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CrossItems, RealVariableCrossItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  bit b;\n"
      "  covergroup cg;\n"
      "    coverpoint b;\n"
      "    x: cross r, b;\n"
      "    rc: coverpoint r { bins a = {[0.0:1.0]}; }\n"
      "    y: cross rc, b;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'r' is a real variable, which a cross "
                            "can reach only through a coverpoint",
                            6, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossItems, CrossItemNamingNoCoverpointOrVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  bit pv;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  bit a, b;\n"
      "  covergroup g1;\n"
      "    ca: coverpoint a;\n"
      "  endgroup\n"
      "  covergroup g2 (ref bit f);\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb;\n"
      "    y: cross a, cb;\n"
      "    z: cross pv, f;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'ca' is neither a coverpoint of "
                            "covergroup 'g2' nor a variable",
                            12, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossBinExpressions, NonConstantReadOrRestrictedCallIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  int lim;\n"
      "  function int count(); static int n = 0; n++; return n; endfunction\n"
      "  covergroup cg (int hi);\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    X: cross a, b {\n"
      "      bins lo = binsof(a) intersect {[0:lim]};\n"
      "      bins c = binsof(b) intersect {count()};\n"
      "      bins h = binsof(a) intersect {[0:hi]};\n"
      "      bins eq = X with (a == b) matches lim;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {9u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'lim' is no constant and cannot be read in a "
                              "covergroup_expression",
                              line, "19.5"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'count' keeps state or has a side "
                            "effect and cannot be called in a "
                            "covergroup_expression",
                            10, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CrossItems, AClassCovergroupCannotCrossARealPropertyDirectly) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class K;\n"
      "    real r; bit [1:0] q;\n"
      "    covergroup kg;\n"
      "      cq: coverpoint q;\n"
      "      cr: coverpoint r { bins lo = {[0.0:1.0]}; }\n"
      "      ok: cross cq, cr;\n"
      "      bad: cross cq, r;\n"
      "    endgroup\n"
      "    function new(); kg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'r' is a real variable, which a cross "
                            "can reach only through a coverpoint",
                            8, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossItems, AClassCovergroupCannotCrossAnotherCovergroupsCoverpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class K;\n"
      "    bit [1:0] q, s;\n"
      "    covergroup g1; c1: coverpoint q; endgroup\n"
      "    covergroup g2;\n"
      "      c2: coverpoint s;\n"
      "      ok: cross c2, q;\n"
      "      bad: cross c2, c1;\n"
      "    endgroup\n"
      "    function new(); g1 = new; g2 = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'c1' is neither a coverpoint of "
                            "covergroup 'g2' nor a variable",
                            8, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossItems, AnExtendedCovergroupCrossesOnlyItsBasesCoverpoints) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class B;\n"
      "    bit [1:0] q, s;\n"
      "    covergroup g1; c1: coverpoint q; endgroup\n"
      "    covergroup g2; c2: coverpoint s; endgroup\n"
      "    function new(); g1 = new; g2 = new; endfunction\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    covergroup extends g2;\n"
      "      ok: cross c2, s;\n"
      "      bad: cross c2, c1;\n"
      "    endgroup\n"
      "    function new(); super.new(); g2 = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'c1' is neither a coverpoint of "
                            "covergroup 'g2' nor a variable",
                            11, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossBodyFunctions, DISABLED_AFunctionOfACrossIsNotVisibleOutsideIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    X: cross ca, cb {\n"
      "      bins early = mk();\n"
      "      function CrossQueueType mk(); mk.push_back('{1, 1}); "
      "endfunction\n"
      "    }\n"
      "    Y: cross ca, cb { bins other = mk(); }\n"
      "  endgroup\n"
      "  initial void'(mk());\n"
      "endmodule\n",
      f);
  for (uint32_t line : {9u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "function 'mk' is declared in cross 'X' and is "
                              "not visible outside it",
                              line, "19.6"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CrossNames, DISABLED_ABareCrossNameOutsideItsCovergroupIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] x, y;\n"
      "  covergroup cg; a: coverpoint x; b: coverpoint y; crs: cross a, b;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial $display(\"%0d\", c.crs.option.weight);\n"
      "  initial $display(\"%0d\", cg::crs::type_option.weight);\n"
      "  initial $display(\"%0d\", crs.option.weight);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross 'crs' is named only after a covergroup "
                            "variable or the covergroup type's '::'",
                            8, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossBinExpressions, DISABLED_ARestrictedReadInACrossIffIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b; int lim; int st;\n"
      "  function automatic bit sidef(); st++; return 1; endfunction\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    X: cross ca, cb iff (lim > 0) {\n"
      "      bins s1 = binsof(ca) iff (sidef());\n"
      "      bins ok = binsof(cb) iff (ca < cb);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'lim' is no constant and cannot be read in a "
                            "covergroup_expression",
                            6, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'sidef' keeps state or has a side "
                            "effect and cannot be called in a "
                            "covergroup_expression",
                            7, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CrossBinExpressions, ARestrictedReadInsideACrossWithIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b; int lim; int st;\n"
      "  function automatic bit outf(output int o); o = 1; return 1; "
      "endfunction\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    X: cross ca, cb {\n"
      "      bins s2 = X with (ca < lim);\n"
      "      bins s3 = binsof(ca) with (outf(st));\n"
      "      bins ok = X with (ca < cb);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'lim' is no constant and cannot be read in a "
                            "covergroup_expression",
                            7, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'outf' has an output, inout or ref "
                            "argument and cannot be called in a "
                            "covergroup_expression",
                            8, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'st' is no constant and cannot be read in a "
                            "covergroup_expression",
                            8, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
