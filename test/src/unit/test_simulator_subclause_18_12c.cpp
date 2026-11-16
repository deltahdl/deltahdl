#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string RunAllTops(const std::string& src) {
  SimFixture f;
  return RunCaptureAllTops(src, f);
}

TEST(ScopeRandomizeCases, AnUnnamedModuleVariableTheBlockReadsKeepsItsValue) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  bit [7:0] lim = 12;\n"
                   "  bit [7:0] a;\n"
                   "  initial begin\n"
                   "    int ok;\n"
                   "    ok = std::randomize(a) with { a < lim; lim == 12; };\n"
                   "    $display(\"%0d %0d %0d\", ok, a < 12, lim);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 1 12\n");
}

TEST(ScopeRandomizeCases, APackageFunctionDrawsAPackageAndALocalVariable) {
  EXPECT_EQ(
      RunSrc("package q;\n"
             "  bit [7:0] pv;\n"
             "  function automatic int draw();\n"
             "    bit [7:0] lv;\n"
             "    void'(std::randomize(pv, lv) with { pv == 31; lv == 32; "
             "});\n"
             "    return lv;\n"
             "  endfunction\n"
             "endpackage\n"
             "module t;\n"
             "  initial begin\n"
             "    int got;\n"
             "    got = q::draw();\n"
             "    $display(\"%0d %0d\", q::pv, got);\n"
             "  end\n"
             "endmodule\n"),
      "31 32\n");
}

TEST(ScopeRandomizeCases, AnInterfaceFunctionDrawsAnInterfaceVariable) {
  EXPECT_EQ(RunSrc("interface ifc;\n"
                   "  bit [7:0] iv;\n"
                   "  function automatic int draw();\n"
                   "    return std::randomize(iv) with { iv == 33; };\n"
                   "  endfunction\n"
                   "endinterface\n"
                   "module t;\n"
                   "  ifc u();\n"
                   "  initial begin\n"
                   "    int ok;\n"
                   "    ok = u.draw();\n"
                   "    $display(\"%0d %0d\", ok, u.iv);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 33\n");
}

TEST(ScopeRandomizeCases, AProgramInitialBlockDrawsAProgramVariable) {
  EXPECT_EQ(RunAllTops("program p;\n"
                       "  bit [7:0] pv;\n"
                       "  initial begin\n"
                       "    int ok;\n"
                       "    ok = std::randomize(pv) with { pv == 34; };\n"
                       "    $display(\"%0d %0d\", ok, pv);\n"
                       "  end\n"
                       "endprogram\n"),
            "1 34\n");
}

TEST(ScopeRandomizeCases, DISABLED_AnEnumArgumentTakesOneOfItsValues) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  typedef enum bit [2:0] {A = 1, B = 4, C = 6} e_t;\n"
                   "  e_t e;\n"
                   "  int named = 0, ok = 0;\n"
                   "  initial begin\n"
                   "    repeat (32) begin\n"
                   "      if (std::randomize(e)) ok++;\n"
                   "      if (e == A || e == B || e == C) named++;\n"
                   "    end\n"
                   "    $display(\"%0d %0d\", ok, named);\n"
                   "  end\n"
                   "endmodule\n"),
            "32 32\n");
}

TEST(ScopeRandomizeCases, ANoArgumentCheckWithOneFalseExpressionReturnsZero) {
  EXPECT_EQ(
      RunSrc("module t;\n"
             "  bit [7:0] a = 3, b = 9;\n"
             "  initial begin\n"
             "    int ok;\n"
             "    ok = std::randomize() with { a == 3; b > a; b == 1; a < "
             "b; };\n"
             "    $display(\"%0d %0d %0d\", ok, a, b);\n"
             "  end\n"
             "endmodule\n"),
      "0 3 9\n");
}

TEST(ScopeRandomizeCases, DISABLED_AnUnpackedArrayArgumentIsRandomized) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [7:0] u[4];\n"
                       "  int i, ok = 0, moved = 0, pinned = 0;\n"
                       "  initial begin\n"
                       "    for (i = 0; i < 8; i++) begin\n"
                       "      ok += std::randomize(u);\n"
                       "      if (u[0] != 0 || u[1] != 0 || u[2] != 0 || u[3] "
                       "!= 0) moved++;\n"
                       "      if (std::randomize(u) with { u[1] == 77; } && "
                       "u[1] == 77) pinned++;\n"
                       "    end\n"
                       "    $display(\"%0d %0d %0d\", ok, moved, pinned);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "8 8 8\n");
}

}  // namespace
