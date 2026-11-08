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

}  // namespace
