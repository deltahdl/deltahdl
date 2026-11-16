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

const char* const kSequence =
    "randsequence(main)\n"
    "      main : first second;\n"
    "      first : { s = {s, \"f\"}; } ;\n"
    "      second : { s = {s, \"s\"}; } ;\n"
    "    endsequence\n";

TEST(RandsequenceCases, AStatementInAClassMethodGeneratesItsSequence) {
  EXPECT_EQ(RunSrc(std::string("class C;\n"
                               "  string s;\n"
                               "  task go();\n"
                               "    ") +
                   kSequence +
                   "  endtask\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    o.go();\n"
                   "    $display(\"%s\", o.s);\n"
                   "  end\n"
                   "endmodule\n"),
            "fs\n");
}

TEST(RandsequenceCases, AStatementInAProgramGeneratesItsSequence) {
  EXPECT_EQ(RunAllTops(std::string("program pg;\n"
                                   "  string s;\n"
                                   "  initial begin\n"
                                   "    ") +
                       kSequence +
                       "    $display(\"%s\", s);\n"
                       "  end\n"
                       "endprogram\n"),
            "fs\n");
}

TEST(RandsequenceCases, AStatementInAnInterfaceGeneratesItsSequence) {
  EXPECT_EQ(RunSrc(std::string("interface ifc;\n"
                               "  string s;\n"
                               "  initial begin\n"
                               "    ") +
                   kSequence +
                   "  end\n"
                   "endinterface\n"
                   "module t;\n"
                   "  ifc u();\n"
                   "  initial #1 $display(\"%s\", u.s);\n"
                   "endmodule\n"),
            "fs\n");
}

TEST(RandsequenceCases, APackageParameterWeightOfZeroIsNeverChosen) {
  EXPECT_EQ(RunSrc("package p;\n"
                   "  parameter int W = 0;\n"
                   "endpackage\n"
                   "module t;\n"
                   "  int i, as = 0, bs = 0;\n"
                   "  initial begin\n"
                   "    for (i = 0; i < 50; i++)\n"
                   "      randsequence(main)\n"
                   "        main : a := p::W | b := 1;\n"
                   "        a : { as++; } ;\n"
                   "        b : { bs++; } ;\n"
                   "      endsequence\n"
                   "    $display(\"%0d %0d\", as, bs);\n"
                   "  end\n"
                   "endmodule\n"),
            "0 50\n");
}

TEST(RandsequenceCases, DISABLED_ACaseProductionComparesUnknownBitsExactly) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  logic [1:0] v = 2'b1x;\n"
                   "  string s;\n"
                   "  initial begin\n"
                   "    randsequence(main)\n"
                   "      main : case (v) 2'b10 : ten; 2'b1x : unknown; "
                   "default : other; endcase ;\n"
                   "      ten : { s = \"ten\"; } ;\n"
                   "      unknown : { s = \"unknown\"; } ;\n"
                   "      other : { s = \"other\"; } ;\n"
                   "    endsequence\n"
                   "    $display(\"%s\", s);\n"
                   "  end\n"
                   "endmodule\n"),
            "unknown\n");
}

TEST(RandsequenceCases, AnUnknownIfConditionGeneratesTheElseItem) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  logic c = 1'bx;\n"
                   "  string s;\n"
                   "  initial begin\n"
                   "    randsequence(main)\n"
                   "      main : if (c) yes else no ;\n"
                   "      yes : { s = \"yes\"; } ;\n"
                   "      no : { s = \"no\"; } ;\n"
                   "    endsequence\n"
                   "    $display(\"%s\", s);\n"
                   "  end\n"
                   "endmodule\n"),
            "no\n");
}

TEST(RandsequenceCases, DISABLED_OutputAndInoutFormalsCopyBack) {
  EXPECT_EQ(
      RunSrc("module t;\n"
             "  int o = 0, io = 4;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : put(o, io) ;\n"
             "      put(output int a, inout int b) : { a = 7; b = b + 1; } "
             ";\n"
             "    endsequence\n"
             "    $display(\"%0d %0d\", o, io);\n"
             "  end\n"
             "endmodule\n"),
      "7 5\n");
}

TEST(RandsequenceCases, DISABLED_RefAndConstRefFormalsAliasTheActual) {
  EXPECT_EQ(
      RunSrc("module t;\n"
             "  int r = 0, seen = 0;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : touch(r, r) ;\n"
             "      touch(ref int a, const ref int c) : { a = 9; seen = c; "
             "} ;\n"
             "    endsequence\n"
             "    $display(\"%0d %0d\", r, seen);\n"
             "  end\n"
             "endmodule\n"),
      "9 9\n");
}

TEST(RandsequenceCases,
     DISABLED_AnInputFormalIsWritableAndLeavesTheActualAlone) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  int k = 3, seen = 0;\n"
                   "  initial begin\n"
                   "    randsequence(main)\n"
                   "      main : take(k) ;\n"
                   "      take(int a) : { a = a + 1; seen = a; } ;\n"
                   "    endsequence\n"
                   "    $display(\"%0d %0d\", k, seen);\n"
                   "  end\n"
                   "endmodule\n"),
            "3 4\n");
}

}  // namespace
