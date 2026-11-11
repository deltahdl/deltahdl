#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ArrayOperationSimulation,
     PackedArrayIsReadWrittenSlicedComparedAndUsedAsAnInteger) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic [7:0] A, B;\n"
                       "  int i = 1, j = 2;\n"
                       "  int r;\n"
                       "  initial begin\n"
                       "    B = 8'hA5;\n"
                       "    A = B;\n"
                       "    $display(\"%h\", A);\n"
                       "    A[i] = B[j];\n"
                       "    A[0] = B[1];\n"
                       "    $display(\"%h\", A);\n"
                       "    A[i +: 2] = B[j +: 2];\n"
                       "    $display(\"%h %0d %0d %0d\", A, A == B, A[i +: 2] "
                       "!= B[j +: 2], A[7:4] == B[7:4]);\n"
                       "    A = 8'b11111111;\n"
                       "    r = A + 3;\n"
                       "    $display(\"%0d\", r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a5\n"
            "a6\n"
            "a2 0 0 1\n"
            "258\n");
}

TEST(ArrayOperationSimulation,
     FixedUnpackedArrayIsReadWrittenSlicedAndCompared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int UA [4], UB [4], UC [4];\n"
                       "  int i = 1, j = 2;\n"
                       "  initial begin\n"
                       "    UB = '{1, 2, 3, 4};\n"
                       "    UA = UB;\n"
                       "    UC = UA;\n"
                       "    $display(\"%p %0d %0d\", UA, UA == UB, UC != UB);\n"
                       "    UA[i] = UB[j];\n"
                       "    $display(\"%p\", UA);\n"
                       "    UA[i +: 2] = UB[j +: 2];\n"
                       "    $display(\"%p %0d %0d %0d\", UA, UA == UB, UA[i +: "
                       "2] != UB[j +: 2],\n"
                       "             UA[0 +: 2] == UB[0 +: 2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{1, 2, 3, 4} 1 0\n"
            "'{1, 3, 3, 4}\n"
            "'{1, 3, 4, 4} 0 0 0\n");
}

TEST(ArrayOperationSimulation,
     DynamicArrayQueueAndAssociativeArrayAreReadAndWrittenWholeAndByElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int DA [], DB [];\n"
                       "  int QA [$], QB [$];\n"
                       "  int AA [string], AB [string];\n"
                       "  int i = 1, j = 2;\n"
                       "  initial begin\n"
                       "    DB = '{5, 6, 7};\n"
                       "    DA = DB;\n"
                       "    DA[i] = DB[j];\n"
                       "    $display(\"%p %p\", DA, DB);\n"
                       "    QB = '{5, 6, 7};\n"
                       "    QA = QB;\n"
                       "    QA[i] = QB[j];\n"
                       "    $display(\"%p %p\", QA, QB);\n"
                       "    AB[\"x\"] = 1;\n"
                       "    AB[\"y\"] = 2;\n"
                       "    AA = AB;\n"
                       "    AA[\"x\"] = AB[\"y\"];\n"
                       "    $display(\"%0d %0d %0d %0d\", AA.num(), AA[\"x\"], "
                       "AB[\"x\"], AA[\"x\"] != AB[\"x\"]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{5, 7, 7} '{5, 6, 7}\n"
            "'{5, 7, 7} '{5, 6, 7}\n"
            "2 2 1 1\n");
}

TEST(ArrayOperationSimulation,
     DISABLED_VariableSizeArraysAreComparedElementByElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int DA [], DB [];\n"
                       "  int QA [$], QB [$];\n"
                       "  int AA [string], AB [string];\n"
                       "  initial begin\n"
                       "    DA = '{1, 2};\n"
                       "    DB = '{1, 3};\n"
                       "    $display(\"%0d %0d\", DA == DB, DA != DB);\n"
                       "    DB = '{1, 2};\n"
                       "    $display(\"%0d %0d\", DA == DB, DA != DB);\n"
                       "    QA = '{1, 2};\n"
                       "    QB = '{1, 3};\n"
                       "    $display(\"%0d %0d\", QA == QB, QA != QB);\n"
                       "    AA[\"a\"] = 1;\n"
                       "    AB[\"a\"] = 2;\n"
                       "    $display(\"%0d %0d\", AA == AB, AA != AB);\n"
                       "    AB[\"a\"] = 1;\n"
                       "    $display(\"%0d %0d\", AA == AB, AA != AB);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 1\n"
            "1 0\n"
            "0 1\n"
            "0 1\n"
            "1 0\n");
}

TEST(ArrayOperationSimulation,
     DISABLED_ConstantWidthSliceIsWrittenIntoADynamicArrayAndAQueue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int DA [], DB [];\n"
                       "  int QA [$], QB [$];\n"
                       "  int i = 0;\n"
                       "  initial begin\n"
                       "    DA = '{1, 2, 3};\n"
                       "    DB = '{7, 8, 9};\n"
                       "    DA[0 +: 2] = DB[1 +: 2];\n"
                       "    $display(\"%p\", DA);\n"
                       "    DA[i +: 2] = DB[0 +: 2];\n"
                       "    $display(\"%p\", DA);\n"
                       "    DA[1:2] = DB[0:1];\n"
                       "    $display(\"%p\", DA);\n"
                       "    QA = '{1, 2, 3};\n"
                       "    QB = '{7, 8, 9};\n"
                       "    QA[0 +: 2] = QB[1 +: 2];\n"
                       "    $display(\"%p\", QA);\n"
                       "    QA[1:2] = QB[0:1];\n"
                       "    $display(\"%p\", QA);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{8, 9, 3}\n"
            "'{7, 8, 3}\n"
            "'{7, 7, 8}\n"
            "'{8, 9, 3}\n"
            "'{8, 7, 8}\n");
}

TEST(ArrayOperationSimulation, ElementsOfASignedUnpackedArrayReadSigned) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit signed [7:0] su [2];\n"
                       "  logic signed [3:0] sm [2][2];\n"
                       "  bit signed [7:0] sd [];\n"
                       "  bit signed [7:0] sq [$];\n"
                       "  bit [7:0] uu [2];\n"
                       "  int r;\n"
                       "  initial begin\n"
                       "    su[0] = 8'hFF;\n"
                       "    uu[0] = 8'hFF;\n"
                       "    r = su[0];\n"
                       "    $display(\"%0d\", r);\n"
                       "    r = uu[0];\n"
                       "    $display(\"%0d\", r);\n"
                       "    sm[1][0] = 4'b1000;\n"
                       "    $display(\"%0d\", sm[1][0] < 0);\n"
                       "    sd = new[1];\n"
                       "    sd[0] = 8'hFF;\n"
                       "    sq.push_back(8'hFF);\n"
                       "    r = sd[0];\n"
                       "    $display(\"%0d\", r);\n"
                       "    r = sq[0];\n"
                       "    $display(\"%0d\", r);\n"
                       "    r = su[0][3:0];\n"
                       "    $display(\"%0d\", r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-1\n"
            "255\n"
            "1\n"
            "-1\n"
            "-1\n"
            "15\n");
}

}  // namespace
