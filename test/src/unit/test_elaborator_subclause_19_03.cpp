#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

TEST(CovergroupExtendsScope, ExtendsInAGenerateBlockIsError) {
  ElabFixture gen;
  ElabOk(
      "module m;\n"
      "  if (1) begin : g\n"
      "    covergroup extends base_cg;\n"
      "    endgroup\n"
      "  end\n"
      "endmodule\n",
      gen);
  EXPECT_TRUE(ReportedError(
      gen.diag.Diagnostics(),
      "a covergroup may only use 'extends' inside a class", 3, "19.3"));
}

TEST(CovergroupExtendsScope, DISABLED_ExtendsInEveryOtherScopeIsError) {
  for (const char* scope : {"package", "program", "interface", "checker"}) {
    ElabFixture f;
    ElabOk(std::string(scope) +
               " s;\n"
               "  covergroup extends base_cg;\n"
               "  endgroup\n"
               "end" +
               scope + "\nmodule m; endmodule\n",
           f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a covergroup may only use 'extends' inside a class", 2, "19.3"))
        << scope;
  }
  ElabFixture unit;
  ElabOk(
      "covergroup extends base_cg;\n"
      "endgroup\n"
      "module m; endmodule\n",
      unit);
  EXPECT_TRUE(ReportedError(
      unit.diag.Diagnostics(),
      "a covergroup may only use 'extends' inside a class", 1, "19.3"));
}

const char* const kFormalOfLo =
    "'lo' is a formal of covergroup 'cg', which is not visible through "
    "instance 'c'";

TEST(CovergroupFormals, DISABLED_AFormalReachedByAFullPathIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int v, w;\n"
      "  covergroup cg (int lo);\n"
      "    coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3);\n"
      "  initial w = top.c.lo;\n"
      "endmodule\n"
      "module m2;\n"
      "  int w;\n"
      "  initial w = top.c.lo;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFormalOfLo, 7, "19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFormalOfLo, 11, "19.3"));
}

TEST(CovergroupFormals,
     DISABLED_AnEmbeddedFormalReachedThroughAnObjectIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int x;\n"
      "  covergroup kc (int arg);\n"
      "    coverpoint x { bins b = {[arg:9]}; }\n"
      "  endgroup\n"
      "  function new(); kc = new(1); endfunction\n"
      "endclass\n"
      "module m2;\n"
      "  K k = new;\n"
      "  int w;\n"
      "  initial w = k.kc.arg;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'arg' is a formal of covergroup 'kc', which is "
                            "not visible through instance 'kc'",
                            11, "19.3"));
}

TEST(CovergroupFormals, ACoverpointAndAMethodStayReachableByPath) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int v; real r;\n"
      "  covergroup cg (int lo);\n"
      "    cp: coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3);\n"
      "  initial begin\n"
      "    top.c.sample();\n"
      "    r = top.c.cp.get_inst_coverage();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string RefWrite(const std::string& item) {
  return "module top;\n"
         "  int va, y;\n"
         "  covergroup cg (ref int x);\n"
         "    " +
         item +
         "\n"
         "  endgroup\n"
         "  cg c = new(va);\n"
         "endmodule\n";
}

TEST(CovergroupFormals, DISABLED_AWriteToARefFormalIsError) {
  for (const char* item :
       {"coverpoint y iff ((x = 3) > 0);", "coverpoint y iff ((x += 1) > 0);",
        "coverpoint y iff (x++ > 0);", "coverpoint y iff (--x > 0);",
        "coverpoint (x = 3);", "coverpoint y + (x -= 2);", "coverpoint x++;"}) {
    ElabFixture f;
    ElaborateSrc(RefWrite(item), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "covergroup 'cg' may not write to its ref "
                              "formal 'x'",
                              4, "19.3"))
        << item;
  }
}

TEST(CovergroupFormals, AReadOfARefFormalIsAccepted) {
  for (const char* item :
       {"coverpoint y iff (x > 0);", "coverpoint x;", "coverpoint y + x;"}) {
    ElabFixture f;
    ElaborateSrc(RefWrite(item), f);
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << item;
  }
}

}  // namespace
