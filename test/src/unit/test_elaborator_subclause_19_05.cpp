#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealCoverpointBins, RealCoverpointWithoutBinsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg (real fr);\n"
      "    coverpoint r;\n"
      "    scaled: coverpoint i * 0.5;\n"
      "    sum: coverpoint i + r;\n"
      "    formal: coverpoint fr;\n"
      "    real typed: coverpoint i;\n"
      "    ignored: coverpoint r { ignore_bins z = {0.0}; }\n"
      "    coverpoint i;\n"
      "    int narrowed: coverpoint r;\n"
      "    binned: coverpoint r { option.weight = 2; bins a = {[0.0:1.0]}; }\n"
      "    cmp: coverpoint r > 1.0;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u, 8u, 9u, 10u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "nothing creates bins for a coverpoint of a real "
                      "expression, so declare at least one 'bins' for it",
                      line, "19.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

TEST(RealCoverpointBins, EmbeddedCovergroupsAreCheckedLikeModuleOnes) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class D;\n"
      "    bit w;\n"
      "    covergroup dg;\n"
      "      cw: coverpoint w;\n"
      "      x: cross cw, nope;\n"
      "    endgroup\n"
      "    function new(); dg = new; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "class C;\n"
      "  real r;\n"
      "  covergroup cg;\n"
      "    coverpoint r;\n"
      "  endgroup\n"
      "  function new(); cg = new; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  real mr;\n"
      "  bit b;\n"
      "  class E;\n"
      "    covergroup eg;\n"
      "      coverpoint b;\n"
      "      y: cross mr, b;\n"
      "    endgroup\n"
      "    function new(); eg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'nope' is neither a coverpoint of "
                            "covergroup 'dg' nor a variable",
                            6, "19.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nothing creates bins for a coverpoint of a real "
                            "expression, so declare at least one 'bins' for it",
                            14, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'mr' is a real variable, which a cross "
                            "can reach only through a coverpoint",
                            24, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CoverpointTypes, DataTypeNeitherIntegralNorRealIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  int v;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  covergroup cg;\n"
      "    string s: coverpoint v;\n"
      "    C k: coverpoint v;\n"
      "    int i: coverpoint v;\n"
      "    bit [3:0] b: coverpoint v;\n"
      "    nib_t n: coverpoint v;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "coverpoint 's' is declared with a data type that "
                            "is neither integral nor real",
                            6, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "coverpoint 'k' is declared with a data type that "
                            "is neither integral nor real",
                            7, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CoverpointTypes, ExpressionNeitherIntegralNorRealIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  string s;\n"
      "  C h;\n"
      "  int v;\n"
      "  covergroup cg;\n"
      "    coverpoint s;\n"
      "    hc: coverpoint h;\n"
      "    int ic: coverpoint h;\n"
      "    sl: coverpoint s.len();\n"
      "    coverpoint v;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a coverpoint covers an integral or real "
                              "expression, and this expression is neither",
                              line, "19.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CoverpointTypes, EmbeddedCoverpointOfAStringIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  string s;\n"
      "  bit b;\n"
      "  covergroup cg (string fs);\n"
      "    coverpoint s;\n"
      "    fc: coverpoint fs;\n"
      "    coverpoint b;\n"
      "  endgroup\n"
      "  function new(); cg = new(\"x\"); endfunction\n"
      "endclass\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a coverpoint covers an integral or real "
                              "expression, and this expression is neither",
                              line, "19.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CoverpointBins, IgnoredDefaultBinIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] v;\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins lo = {[0:7]};\n"
      "      ignore_bins rest = default;\n"
      "      ignore_bins rest_seq = default sequence;\n"
      "      bins other = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ignore_bins 'rest' cannot ignore the default bin",
                            6, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ignore_bins 'rest_seq' cannot ignore the default "
                            "bin",
                            7, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CovergroupExpressionNames, NonConstantOrRefReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v, lim;\n"
      "  parameter int P = 4; const int C = 1;\n"
      "  covergroup cg (int ok, ref int r, r2);\n"
      "    coverpoint v {\n"
      "      bins a = {[0:lim]};\n"
      "      bins b = {r};\n"
      "      bins c[lim] = {[0:9]};\n"
      "      bins d = {[0:ok]};\n"
      "      bins e = {[C:P]};\n"
      "      bins t = (lim => 1);\n"
      "      bins w[] = {[0:9]} with (item < lim);\n"
      "      bins x = {r2};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 8u, 11u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'lim' is no constant and cannot be read in a "
                              "covergroup_expression",
                              line, "19.5"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'r' is a ref formal of covergroup 'cg' and cannot "
                            "be read in a covergroup_expression",
                            7, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'r2' is a ref formal of covergroup 'cg' and "
                            "cannot be read in a covergroup_expression",
                            13, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

TEST(CovergroupExpressionCalls, RestrictedCallIsError) {
  ElabFixture f;
  ElaborateSrc(
      "function automatic int uf(int x); return x; endfunction\n"
      "module m;\n"
      "  int v, g;\n"
      "  function automatic int bump(ref int x); x++; return x; endfunction\n"
      "  function int count(); static int n = 0; n++; return n; endfunction\n"
      "  function automatic int outer(); return g; endfunction\n"
      "  function automatic int twice(int x); return 2 * x; endfunction\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins a = {bump(g)};\n"
      "      bins b = {count()};\n"
      "      bins c = {outer()};\n"
      "      bins d = {$urandom()};\n"
      "      bins e = {twice(3), $clog2(16)};\n"
      "      bins f = {uf(2)};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'bump' has an output, inout or ref "
                            "argument and cannot be called in a "
                            "covergroup_expression",
                            10, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'g' is no constant and cannot be read in a "
                            "covergroup_expression",
                            10, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'count' keeps state or has a side "
                            "effect and cannot be called in a "
                            "covergroup_expression",
                            11, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'outer' reads 'g', a variable outside it "
                            "that is no constant, and cannot be called in a "
                            "covergroup_expression",
                            12, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "system function '$urandom' is no constant system "
                            "function and cannot be called in a "
                            "covergroup_expression",
                            13, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

TEST(CovergroupExpressionNames, InstanceConstantInitializedLateIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new();\n"
      "    cg = new;\n"
      "    lim = 7;\n"
      "  endfunction\n"
      "endclass\n"
      "class D;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new();\n"
      "    repeat (1) begin\n"
      "      lim = 7;\n"
      "      cg = new;\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n"
      "class E;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new();\n"
      "    lim = 7;\n"
      "    cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant 'lim', which covergroup 'cg' "
                            "reads, is initialized after the covergroup's new "
                            "in the constructor",
                            5, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant 'lim', which covergroup 'cg' "
                            "reads, is initialized in the same looping "
                            "statement or fork-join_none as the covergroup's "
                            "new",
                            16, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CovergroupExpressionNames, InstanceConstantInABlockOrForkIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class F;\n"
      "  const int lim;\n"
      "  const int top = 9;\n"
      "  bit [3:0] x;\n"
      "  int q[2];\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[lim:top]}; bins t = (1 => 2); }\n"
      "  endgroup\n"
      "  function new();\n"
      "    q[0] = 1;\n"
      "    cg = null;\n"
      "    begin\n"
      "      cg = new;\n"
      "      this.lim = 7;\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n"
      "class G;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new();\n"
      "    fork\n"
      "      lim = 7;\n"
      "      cg = new;\n"
      "    join_none\n"
      "  endfunction\n"
      "endclass\n"
      "class H;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    coverpoint x { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new();\n"
      "    if (x == 0) begin\n"
      "      lim = 7;\n"
      "      cg = new;\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n"
      "class I;\n"
      "  const int lim;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg with function sample(int s);\n"
      "    coverpoint s { bins b = {[0:lim]}; }\n"
      "  endgroup\n"
      "  function new(); cg = new; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant 'lim', which covergroup 'cg' "
                            "reads, is initialized after the covergroup's new "
                            "in the constructor",
                            7, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant 'lim', which covergroup 'cg' "
                            "reads, is initialized in the same looping "
                            "statement or fork-join_none as the covergroup's "
                            "new",
                            22, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CovergroupExpressionNames, EmbeddedCovergroupReadsItsClassAndScope) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int g;\n"
      "  const int K = 2;\n"
      "  function automatic int mf(int a); return a; endfunction\n"
      "  class C;\n"
      "    bit [3:0] x, y;\n"
      "    int v;\n"
      "    parameter int P = 3;\n"
      "    function automatic int cm(int a); return a; endfunction\n"
      "    covergroup cg;\n"
      "      coverpoint x {\n"
      "        bins a = {[0:v]};\n"
      "        bins b = {[0:g]};\n"
      "        bins c = {[K:P]};\n"
      "        bins d = {cm(1), mf(2)};\n"
      "      }\n"
      "      X: cross x, y;\n"
      "    endgroup\n"
      "    function new(); cg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v' is no constant and cannot be read in a "
                            "covergroup_expression",
                            12, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'g' is no constant and cannot be read in a "
                            "covergroup_expression",
                            13, "19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
