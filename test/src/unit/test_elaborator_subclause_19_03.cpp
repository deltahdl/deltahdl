#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CovergroupExtendsScope, ExtendsInModuleError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  covergroup extends base_cg;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a covergroup may only use 'extends' inside a class", 2, "19.3"));
}

TEST(CovergroupExtendsScope, NonExtendsCovergroupInModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [2:0] addr;\n"
             "  covergroup cg @(addr);\n"
             "    coverpoint addr;\n"
             "  endgroup\n"
             "endmodule\n"));
}

TEST(CovergroupExtendsScope, ExtendsInsideClassOk) {
  EXPECT_TRUE(
      ElabOk("class Base; logic clk;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  covergroup extends cg;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(CovergroupNewActuals, FormalWithoutDefaultLeftWithoutActualIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v;\n"
      "  covergroup cg (int lo);\n"
      "    coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  cg d = new(3);\n"
      "  initial begin\n"
      "    automatic cg e = new();\n"
      "    c = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "new of covergroup 'cg' gives no actual to "
                              "formal 'lo', which has no default",
                              line, "19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CovergroupNewActuals, ActualBindingNoFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v;\n"
      "  covergroup cg (int lo);\n"
      "    coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3, 4);\n"
      "  cg d = new(.hi(3));\n"
      "  cg e = new(.lo(3));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "new of covergroup 'cg' is given 2 actuals for its "
                            "1 formals",
                            6, "19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'cg' has no formal 'hi'", 7, "19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "new of covergroup 'cg' gives no actual to formal "
                            "'lo', which has no default",
                            7, "19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CovergroupNewActuals, RefFormalGivenNoVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  int v;\n"
      "  int arr[2];\n"
      "  struct {int f;} s;\n"
      "  covergroup cg (ref int x);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  cg a = new(v + 1);\n"
      "  cg b = new(5);\n"
      "  cg c = new(w);\n"
      "  cg d = new(v);\n"
      "  cg e = new(arr[1]);\n"
      "  cg g = new(s.f);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the actual of ref formal 'x' of covergroup 'cg' "
                              "is no variable",
                              line, "19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CovergroupFormals, FormalReadThroughAnInstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v, w;\n"
      "  wire [3:0] u;\n"
      "  covergroup cg (int lo);\n"
      "    cp: coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3);\n"
      "  assign u = c.lo;\n"
      "  initial begin\n"
      "    w = c.lo;\n"
      "    c.sample();\n"
      "    c.lo.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 10u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'lo' is a formal of covergroup 'cg', which is "
                              "not visible through instance 'c'",
                              line, "19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
