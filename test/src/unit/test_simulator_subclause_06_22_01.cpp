#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MatchingTypeComparisonSim, TypeParameterOverrideMatchesTheTypeItNames) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub #(type T = int);\n"
                       "  localparam bit IsInt = type(T) == type(int);\n"
                       "  localparam bit IsByte = type(T) == type(byte);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  typedef byte word_t;\n"
                       "  sub u0();\n"
                       "  sub #(.T(byte)) u1();\n"
                       "  sub #(.T(word_t)) u2();\n"
                       "  sub #(.T(shortint)) u3();\n"
                       "  initial $display(\"%0d%0d %0d%0d %0d%0d %0d%0d\", "
                       "u0.IsInt, u0.IsByte, u1.IsInt, u1.IsByte, u2.IsInt, "
                       "u2.IsByte, u3.IsInt, u3.IsByte);\n"
                       "endmodule\n",
                       f),
            "10 01 01 00\n");
}

TEST(MatchingTypeComparisonSim, BuiltInComparisonsHoldInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package q;\n"
                 "  localparam bit Same = type(int) == type(int);\n"
                 "  localparam bit Other = type(int) == type(shortint);\n"
                 "  function bit fs;\n"
                 "    return type(byte) == type(byte);\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "localparam bit USame = type(byte) == type(byte);\n"
                 "localparam bit UOther = type(byte) == type(bit [7:0]);\n"
                 "class N;\n"
                 "  localparam bit Same = type(real) == type(real);\n"
                 "  localparam bit Other = type(real) == type(shortreal);\n"
                 "endclass\n"
                 "module top;\n"
                 "  function bit fs;\n"
                 "    return type(longint) == type(longint);\n"
                 "  endfunction\n"
                 "  function bit fo;\n"
                 "    return type(longint) == type(integer);\n"
                 "  endfunction\n"
                 "  if (type(time) == type(time)) begin : g\n"
                 "    localparam bit Other = type(time) == type(int);\n"
                 "  end\n"
                 "  initial $display(\"%0d%0d%0d %0d%0d %0d%0d %0d%0d "
                 "%0d\", q::Same, q::Other, q::fs(), USame, UOther, "
                 "N::Same, N::Other, fs(), fo(), g.Other);\n"
                 "endmodule\n",
                 f),
      "101 10 10 10 0\n");
}

TEST(MatchingTypeComparisonSim, PackageObjectsMatchTheirTypesInsideThePackage) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package q;\n"
                 "  struct packed {int A;} PA1, PA2;\n"
                 "  struct packed {int A;} PA3;\n"
                 "  typedef struct packed {int A;} st;\n"
                 "  st S1;\n"
                 "  int I1;\n"
                 "  localparam bit Same = type(PA1) == type(PA2);\n"
                 "  localparam bit Other = type(PA1) == type(PA3);\n"
                 "  localparam bit Named = type(S1) == type(st);\n"
                 "  localparam bit BuiltIn = type(I1) == type(int);\n"
                 "endpackage\n"
                 "module top;\n"
                 "  initial $display(\"%0d%0d%0d%0d\", q::Same, q::Other, "
                 "q::Named, q::BuiltIn);\n"
                 "endmodule\n",
                 f),
      "1011\n");
}

TEST(MatchingTypeComparisonSim,
     UnitObjectsMatchTheirTypesInTheCompilationUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("struct packed {int A;} UA1, UA2;\n"
                       "struct packed {int A;} UA3;\n"
                       "typedef struct packed {int A;} ust;\n"
                       "ust US1;\n"
                       "byte UI1;\n"
                       "localparam bit USame = type(UA1) == type(UA2);\n"
                       "localparam bit UOther = type(UA1) == type(UA3);\n"
                       "localparam bit UNamed = type(US1) == type(ust);\n"
                       "localparam bit UBuiltIn = type(UI1) == type(byte);\n"
                       "localparam bit UWider = type(UI1) == type(int);\n"
                       "module top;\n"
                       "  initial $display(\"%0d%0d%0d%0d%0d\", USame, UOther, "
                       "UNamed, UBuiltIn, UWider);\n"
                       "endmodule\n",
                       f),
            "10110\n");
}

TEST(MatchingTypeComparisonSim,
     ClassTypeParameterOverrideMatchesTheTypeItNames) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K #(type T = int);\n"
                       "  localparam bit IsInt = type(T) == type(int);\n"
                       "  localparam bit IsByte = type(T) == type(byte);\n"
                       "endclass\n"
                       "module top;\n"
                       "  initial $display(\"%0d%0d %0d%0d\", K#()::IsInt, "
                       "K#()::IsByte, K#(byte)::IsInt, K#(byte)::IsByte);\n"
                       "endmodule\n",
                       f),
            "10 01\n");
}

}  // namespace
