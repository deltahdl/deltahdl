#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(MultidimensionalArraySimulation, PackageArrayOfStagedTypedefIsTwoDim) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef bit [1:5] bsix;\n"
      "  typedef bsix mem_type [0:3];\n"
      "  mem_type ba [0:7];\n"
      "  bsix plain [0:1];\n"
      "  function automatic int f();\n"
      "    ba[0][0] = 5'd7;\n"
      "    ba[0][3] = 5'd1;\n"
      "    return ba[0][0] + ba[0][3];\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = p::f();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 8u);
}

TEST(MultidimensionalArraySimulation, PortArrayOfStagedTypedefIsTwoDim) {
  auto v = RunAndGet(
      "typedef bit [1:5] bsix;\n"
      "typedef bsix mem_type [0:3];\n"
      "typedef bit [7:0] byte_t;\n"
      "module t(output mem_type ba [0:1], output byte_t o [0:1]);\n"
      "  int result;\n"
      "  initial begin\n"
      "    ba[1][2] = 5'd4;\n"
      "    result = ba[1][2] + ba[1][0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

constexpr std::string_view kAggregateTypes =
    "typedef logic [3:0] nib_t;\n"
    "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
    "typedef struct { logic [1:0][3:0] q; ps_t [1:0] pa; } us_t;\n";

constexpr std::string_view kPackedParams =
    "  parameter logic [1:0][3:0] Q = 8'h6C;\n"
    "  parameter logic [0:1][3:0] A = 8'h6C;\n"
    "  parameter logic [1:0][1:0][3:0] R = 16'h1234;\n"
    "  parameter nib_t [1:0] T = 8'h6C;\n"
    "  parameter ps_t [1:0] PA = 16'h1234;\n"
    "  parameter us_t P = '{q: 8'h6C, pa: 16'h1234};\n"
    "  parameter logic [1:0][3:0] E [2] = '{8'h6C, 8'h12};\n"
    "  parameter struct packed {\n"
    "    struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
    "  } [1:0] SP = 16'h1234;\n"
    "  parameter union packed { logic [7:0] w; logic [1:0][3:0] n; } [1:0] UP "
    "=\n"
    "      16'h1234;\n"
    "  parameter struct packed {\n"
    "    struct packed { logic [3:0] hi; logic [3:0] lo; } [1:0][1:0] pb;\n"
    "    struct packed { logic [3:0] hi; logic [3:0] lo; } [1:0] pc;\n"
    "    logic [1:0][1:0][3:0] n;\n"
    "  } M = 64'h9abcdef0_7b6a_5a3c;\n"
    "  localparam V1 = Q[1], V2 = Q[0], V3 = Q[1][2:1], V4 = Q[0][2];\n"
    "  localparam V5 = Q[1:0], V6 = A[0], V7 = A[1];\n"
    "  localparam V8 = R[1], V9 = R[0][1], V10 = R[0][1][1];\n"
    "  localparam V11 = T[1], V12 = PA[1], V13 = PA[1].lo, V14 = PA[0].hi;\n"
    "  localparam V15 = P.q[1], V16 = P.pa[1], V17 = P.pa[1].lo;\n"
    "  localparam V18 = E[1][1], V19 = SP[1].s.lo, V20 = UP[0].n[1];\n"
    "  localparam V21 = M.pb[1][0], V22 = M.pb[1][0].hi, V23 = M.pb[0][1].lo;\n"
    "  localparam V24 = M.pc[1].lo, V25 = M.n[1][0], V26 = M.n[0];\n";

constexpr std::string_view kWidthDecls =
    "  logic [@Q[1]:0] w1;\n"
    "  logic [@Q[1][2:1]:0] w2;\n"
    "  logic [@A[1]:0] w3;\n"
    "  logic [@R[0][1]:0] w4;\n"
    "  logic [@T[1]:0] w5;\n"
    "  logic [@PA[1].lo:0] w6;\n"
    "  logic [@P.q[1]:0] w7;\n"
    "  logic [@P.pa[1].lo:0] w8;\n"
    "  logic [@E[1][1]:0] w9;\n"
    "  logic [@SP[1].s.lo:0] w10;\n"
    "  logic [@UP[0].n[1]:0] w11;\n"
    "  logic [@M.pb[1][0].hi:0] w12;\n"
    "  logic [@M.n[1][0]:0] w13;\n";

constexpr std::string_view kGenerateCheck =
    "  if (@Q[1] == 6 && @Q[0] == 12 && @A[0] == 6 && @R[0][1] == 3 &&\n"
    "      @T[1] == 6 && @PA[1].lo == 2 && @P.q[1] == 6 &&\n"
    "      @P.pa[1].lo == 2 && @E[1][1] == 1 && @R[1] == 8'h12 &&\n"
    "      @PA[1] == 8'h12 && @P.pa[1] == 8'h12 && @SP[1].s.lo == 2 &&\n"
    "      @UP[0].n[1] == 3 && @M.pb[1][0] == 8'hbc &&\n"
    "      @M.pb[0][1].lo == 14 && @M.pc[1].lo == 11 &&\n"
    "      @M.n[1][0] == 10) begin : g\n"
    "    initial #1 $display(\"gen ok\");\n"
    "  end\n";

constexpr std::string_view kValueDisplays =
    "    $display(\"%0d %0d %0d %0d %0d\", $bits(@V1), $bits(@V5),\n"
    "             $bits(@V8), $bits(@V12), $bits(@V16));\n"
    "    $display(\"%h %h %h %h %h %h %h\", @V1, @V2, @V3, @V4, @V5, @V6,\n"
    "             @V7);\n"
    "    $display(\"%h %h %h %h %h %h %h\", @V8, @V9, @V10, @V11, @V12,\n"
    "             @V13, @V14);\n"
    "    $display(\"%h %h %h %h %h %h\", @V15, @V16, @V17, @V18, @V19,\n"
    "             @V20);\n"
    "    $display(\"%0d %h %h %h %h %h %h\", $bits(@V21), @V21, @V22, @V23,\n"
    "             @V24, @V25, @V26);\n";

constexpr std::string_view kDirectReads =
    "    $display(\"%h %h %h %h %h %h %h %h\", @Q[1], @PA[1].lo, @P.pa[1].lo,\n"
    "             @E[1][1], @SP[1].s.lo, @UP[0].n[1], @M.pc[1][2],\n"
    "             @M.n[0][1][1]);\n"
    "    $display(\"%h %h %h %h %h %h %0d\", @M.pb[1][0], @M.pb[1][0].hi,\n"
    "             @M.pb[0][1].lo, @M.pc[1].lo, @M.n[1][0], @M.n[0],\n"
    "             $bits(@M.pb[1][0]));\n";

constexpr std::string_view kWidthDisplay =
    "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d\",\n"
    "             $bits(w1), $bits(w2), $bits(w3), $bits(w4), $bits(w5),\n"
    "             $bits(w6), $bits(w7), $bits(w8), $bits(w9), $bits(w10),\n"
    "             $bits(w11), $bits(w12), $bits(w13));\n";

constexpr std::string_view kValueLines =
    "4 8 8 8 8\n"
    "6 c 3 1 6c 6 c\n"
    "12 3 1 6 12 2 3\n"
    "6 12 2 1 2 3\n"
    "8 bc b e b a 3c\n";

constexpr std::string_view kDirectLine =
    "6 2 2 1 2 3 0 1\n"
    "bc b e b a 3c 8\n";

constexpr std::string_view kWidthLine = "7 4 13 4 7 3 7 3 2 3 4 12 11\n";

std::string Prefixed(std::string_view text, std::string_view prefix) {
  std::string out;
  for (char c : text) {
    if (c == '@') {
      out += prefix;
    } else {
      out += c;
    }
  }
  return out;
}

constexpr std::string_view kNamedElementMembers =
    "struct packed {\n"
    "    ps_t [1:0][1:0] pq;\n"
    "    logic [1:0][1:0][3:0] n;\n"
    "  } MQ = 48'h12345678_5a3c;\n";

std::string NamedElementParam() {
  return "  localparam " + std::string(kNamedElementMembers);
}

constexpr std::string_view kNamedElementReads =
    "  localparam W1 = @MQ.pq[1][0], W2 = @MQ.pq[1][0].hi;\n"
    "  logic [@MQ.pq[1][0].hi:0] wq;\n"
    "  if (@MQ.pq[1][0] == 8'h34 && @MQ.n[1][1] == 5) begin : gq\n"
    "    initial #2 $display(\"gq ok\");\n"
    "  end\n"
    "  initial #3 $display(\"mq %h %h %h %h %h %0d %0d\", W1, W2,\n"
    "                      @MQ.pq[1][0], @MQ.n[0], @MQ.n[1][0], $bits(W1),\n"
    "                      $bits(wq));\n";

constexpr std::string_view kNamedElementLines = "gq ok\nmq 34 3 34 3c a 8 4\n";

std::string ReadsThrough(std::string_view prefix) {
  return Prefixed(kWidthDecls, prefix) + Prefixed(kGenerateCheck, prefix) +
         "  initial begin\n" + Prefixed(kValueDisplays, prefix) +
         Prefixed(kDirectReads, prefix) + std::string(kWidthDisplay) +
         "  end\n";
}

std::string MatrixOutput() {
  return std::string(kValueLines) + std::string(kDirectLine) +
         std::string(kWidthLine) + "gen ok\n" + std::string(kNamedElementLines);
}

std::string MatrixParams() {
  return std::string(kPackedParams) + "  parameter " +
         std::string(kNamedElementMembers);
}

std::string MatrixReads(std::string_view prefix) {
  return ReadsThrough(prefix) + Prefixed(kNamedElementReads, prefix);
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInAModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAggregateTypes) + "module t;\n" +
                           MatrixParams() + MatrixReads("") + "endmodule\n",
                       f),
            MatrixOutput());
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInAPackage) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAggregateTypes) + "package pk;\n" +
                           MatrixParams() + "endpackage\n" + "module t;\n" +
                           MatrixReads("pk::") + "endmodule\n",
                       f),
            MatrixOutput());
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInTheCompilationUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAggregateTypes) + MatrixParams() +
                           "module t;\n" + MatrixReads("") + "endmodule\n",
                       f),
            MatrixOutput());
}

TEST(PackedParameterSelectSim, SelectsUnderAnUnpackedMemberElementReachIt) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("typedef struct { logic [7:0] a; logic [1:0][3:0] u [2]; } "
                 "um_t;\n"
                 "parameter um_t CP = '{a: 8'h11, u: '{8'h6C, 8'h12}};\n"
                 "module t;\n"
                 "  parameter um_t P = '{a: 8'h11, u: '{8'h6C, 8'h12}};\n"
                 "  localparam V1 = P.u[1][0], V2 = CP.u[0][1];\n"
                 "  logic [P.u[1][0]:0] w;\n"
                 "  initial $display(\"%h %h %h %h %h %h %0d %0d\", V1, V2,\n"
                 "                   P.u[1][0], P.u[0], CP.u[0][1], CP.u[1],\n"
                 "                   $bits(P.u[1][0]), $bits(w));\n"
                 "endmodule\n",
                 f),
      "2 6 2 6c 6 12 4 3\n");
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInAClassBody) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kAggregateTypes) + "class C;\n" +
                     std::string(kPackedParams) + Prefixed(kWidthDecls, "") +
                     "  static function void s();\n" +
                     Prefixed(kValueDisplays, "") + Prefixed(kDirectReads, "") +
                     "  endfunction\n"
                     "  function void i();\n" +
                     std::string(kWidthDisplay) +
                     "  endfunction\n"
                     "endclass\n"
                     "module t;\n"
                     "  C c;\n" +
                     Prefixed(kGenerateCheck, "C::") +
                     "  initial begin\n"
                     "    C::s();\n"
                     "    c = new;\n"
                     "    c.i();\n" +
                     Prefixed(kValueDisplays, "C::") +
                     Prefixed(kDirectReads, "C::") +
                     "  end\n"
                     "endmodule\n",
                 f),
      std::string(kValueLines) + std::string(kDirectLine) +
          std::string(kWidthLine) + std::string(kValueLines) +
          std::string(kDirectLine) + "gen ok\n");
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInAClassParameterPort) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          std::string(kAggregateTypes) +
              "class D #(parameter logic [1:0][3:0] HQ = 8'h6C,\n"
              "          parameter ps_t [1:0] HP = 16'h1234,\n"
              "          parameter ps_t HS = 8'h56,\n"
              "          parameter logic [1:0][3:0] HE [2] = '{8'h6C, "
              "8'h12},\n"
              "          parameter struct packed {\n"
              "            logic [3:0] hi; logic [3:0] lo;\n"
              "          } [1:0] HSP = 16'h1234,\n"
              "          parameter struct packed {\n"
              "            logic [1:0][1:0][3:0] n;\n"
              "          } HM = 16'h5a3c);\n"
              "  localparam V1 = HQ[1], V2 = HP[0].hi, V3 = HS.lo;\n"
              "  localparam V4 = HE[1][1], V5 = HE[0];\n"
              "  logic [HQ[1]:0] w1;\n"
              "  logic [HP[0].hi:0] w2;\n"
              "  logic [HE[0][1]:0] w3;\n"
              "  static logic [HQ[0]:0] sw;\n"
              "  static function void s();\n"
              "    $display(\"%h %h %h %h %h %h %h %h %h\", V1, V2, V3, V4, "
              "V5,\n"
              "             HQ[1], HP[0].hi, HS.hi, HE[1][1]);\n"
              "  endfunction\n"
              "  function void i();\n"
              "    $display(\"%0d %0d %0d %0d\", $bits(w1), $bits(w2), "
              "$bits(w3),\n"
              "             $bits(sw));\n"
              "  endfunction\n"
              "endclass\n"
              "class E extends D;\n"
              "  static function void t();\n"
              "    $display(\"e %h %h %h %h %h\", HQ[1], HSP[1].lo, HSP[0],\n"
              "             HM.n[0], HM.n[1][0]);\n"
              "  endfunction\n"
              "endclass\n"
              "module t;\n"
              "  D d1;\n"
              "  D #(8'h3A, 16'h5678, 8'h9B, '{8'h21, 8'h43}) d2;\n"
              "  if (D#()::HQ[1] == 6 && D#()::HP[0].hi == 3 &&\n"
              "      D#()::HE[1][1] == 1) begin : g\n"
              "    initial #1 $display(\"gen ok\");\n"
              "  end\n"
              "  initial begin\n"
              "    D#()::s();\n"
              "    d1 = new;\n"
              "    d1.i();\n"
              "    D#(8'h3A, 16'h5678, 8'h9B, '{8'h21, 8'h43})::s();\n"
              "    d2 = new;\n"
              "    d2.i();\n"
              "    $display(\"m %h %h %h %h %h\", D#()::HS.hi, "
              "D#()::HP[0].hi,\n"
              "             D#()::HQ[1], D#()::HE[1][1], D#()::HSP[1].lo);\n"
              "    E::t();\n"
              "  end\n"
              "endmodule\n",
          f),
      "6 3 6 1 6c 6 3 5 1\n"
      "7 4 7 13\n"
      "3 7 b 4 21 3 7 9 4\n"
      "4 8 3 11\n"
      "m 5 3 6 1 2\n"
      "e 6 2 34 3c a\n"
      "gen ok\n");
}

constexpr std::string_view kUnpackedShapes =
    "  parameter logic [1:0][3:0] E2 [2][2] = '{'{8'h12, 8'h34},\n"
    "                                          '{8'h56, 8'h78}};\n"
    "  parameter logic [1:0][3:0] A [2] = '{8'h6C, 8'h9A};\n"
    "  parameter logic [1:0][3:0] B [2] = A;\n";

TEST(PackedParameterSelectSim, SelectsFoldThroughEveryUnpackedShape) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class C;\n" + std::string(kUnpackedShapes) +
              "  static logic [E2[1][0][1]:0] w;\n"
              "  static logic [B[0][1]:0] wb;\n"
              "  static bit [B[0][1]:0] wbit;\n"
              "  static logic [2*B[0][1]-1:0][1:0] w2;\n"
              "  static function void s();\n"
              "    $display(\"c %h %h %h %h %0d %0d %0d %0d\", E2[1][0][1],\n"
              "             E2[0][1], B[0][1], B[1], $bits(w), $bits(wb),\n"
              "             $bits(wbit), $bits(w2));\n"
              "  endfunction\n"
              "endclass\n"
              "module t;\n" +
              std::string(kUnpackedShapes) +
              "  logic [E2[1][0][1]:0] w;\n"
              "  logic [B[0][1]:0] wb;\n"
              "  logic [2*B[0][1]-1:0][1:0] w2;\n"
              "  initial begin\n"
              "    $display(\"m %h %h %h %h %0d %0d %0d\", E2[1][0][1], "
              "E2[0][1],\n"
              "             B[0][1], B[1], $bits(w), $bits(wb), $bits(w2));\n"
              "    C::s();\n"
              "  end\n"
              "endmodule\n",
          f),
      "m 5 34 6 9a 6 7 24\n"
      "c 5 34 6 9a 6 7 7 24\n");
}

TEST(PackedParameterSelectSim, SelectsFoldToTheSubarrayInEveryOtherScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          std::string(kAggregateTypes) +
              "interface ifc;\n"
              "  parameter logic [1:0][3:0] Q = 8'h6C;\n"
              "  parameter ps_t [1:0] PA = 16'h1234;\n"
              "  localparam V1 = Q[1], V2 = PA[1].lo;\n" +
              NamedElementParam() +
              "  logic [Q[0]:0] w;\n"
              "  if (Q[1] == 6 && PA[0].hi == 3 && MQ.n[1][1] == 5) begin : g\n"
              "    initial $display(\"ifc gen ok\");\n"
              "  end\n"
              "  initial #1 $display(\"ifc %h %h %0d %h %h\", V1, V2, "
              "$bits(w),\n"
              "                      MQ.pq[1][0], MQ.n[0]);\n"
              "endinterface\n"
              "program pg;\n"
              "  parameter logic [1:0][3:0] Q = 8'h6C;\n"
              "  localparam V1 = Q[1], V3 = Q[1][2:1];\n"
              "  logic [Q[1]:0] w;\n"
              "  initial #9 $display(\"pg %h %h %0d\", V1, V3, $bits(w));\n"
              "endprogram\n"
              "module t;\n"
              "  ifc i();\n"
              "  pg p();\n"
              "  for (genvar k = 0; k < 1; k++) begin : gb\n"
              "    parameter logic [1:0][3:0] Q = 8'h6C;\n"
              "    localparam V1 = Q[1];\n" +
              NamedElementParam() +
              "    logic [Q[1]:0] w;\n"
              "    initial #3 $display(\"gb %h %0d %h %h\", V1, $bits(w),\n"
              "                        MQ.pq[1][0], MQ.n[0]);\n"
              "  end\n"
              "  function automatic int f();\n"
              "    localparam logic [1:0][3:0] Q = 8'h6C;\n"
              "    localparam V1 = Q[1];\n"
              "    logic [Q[1]:0] w;\n"
              "    return V1 * 100 + $bits(w);\n"
              "  endfunction\n"
              "  task automatic tk();\n"
              "    localparam logic [1:0][3:0] Q = 8'h6C;\n"
              "    logic [Q[0]:0] w;\n"
              "    $display(\"tk %h %0d\", Q[0], $bits(w));\n"
              "  endtask\n"
              "  initial begin : nb\n"
              "    localparam logic [1:0][3:0] Q = 8'h6C;\n"
              "    localparam V1 = Q[1];\n" +
              NamedElementParam() +
              "    logic [Q[1]:0] w;\n"
              "    #4 $display(\"nb %h %0d f %0d %h %h\", V1, $bits(w), f(),\n"
              "                MQ.pq[1][0], MQ.n[0]);\n"
              "    tk();\n"
              "  end\n"
              "endmodule\n",
          f),
      "ifc gen ok\n"
      "ifc 6 2 13 34 3c\n"
      "gb 6 7 34 3c\n"
      "nb 6 7 f 607 34 3c\n"
      "tk c 13\n"
      "pg 6 3 7\n");
}

TEST(PackedMemberSelectSim, SelectsUnderAVariableMemberReachTheSubarray) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "package pk;\n"
          "  " +
              std::string(kNamedElementMembers) +
              "endpackage\n"
              "module t;\n"
              "  struct packed {\n"
              "    ps_t [1:0][1:0] pq;\n"
              "    struct packed { logic [3:0] hi; logic [3:0] lo; } "
              "[1:0][1:0] "
              "pb;\n"
              "    logic [1:0][1:0][3:0] n;\n"
              "  } v = 80'h12345678_9abcdef0_5a3c;\n"
              "  struct { logic [1:0][3:0] u [2]; } w = '{u: '{8'h6C, "
              "8'h12}};\n"
              "  initial begin : nb\n"
              "    automatic " +
              std::string(kNamedElementMembers) +
              "    $display(\"%h %h %h %h %h %0d %0d\", v.pq[1][0], "
              "v.pq[1][0].hi,\n"
              "             v.pb[0][1].lo, v.n[1][0], w.u[1][0], "
              "$bits(v.pq[1][0]),\n"
              "             $bits(w.u[1][0]));\n"
              "    $display(\"%h %h %h %h\", pk::MQ.pq[1][0], pk::MQ.n[0], "
              "MQ.pq[1][0],\n"
              "             MQ.n[0]);\n"
              "  end\n"
              "endmodule\n",
          f),
      "34 3 e a 2 8 4\n"
      "34 3c 34 3c\n");
}

TEST(PackedParameterSelectSim, SelectsOfOuterParametersSizeAClassProperty) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  parameter logic [1:0][3:0] Q = 8'h6C;\n"
                       "  class P;\n"
                       "    logic [Q[1]:0] a;\n"
                       "  endclass\n"
                       "endpackage\n"
                       "localparam logic [1:0][3:0] U = 8'h3A;\n"
                       "import pk::Q;\n"
                       "class C;\n"
                       "  logic [pk::Q[1]:0] a;\n"
                       "  logic [U[0]:0] b;\n"
                       "  logic [Q[0]-1:0] i;\n"
                       "  logic [$unit::U[0]:0] q;\n"
                       "  logic [0:pk::Q[1]] r;\n"
                       "  logic [1:0][U[0]:0] v;\n"
                       "  static logic [pk::Q[0]-1:0] s;\n"
                       "  localparam logic [pk::Q[1]:0] L = '1;\n"
                       "endclass\n"
                       "module t;\n"
                       "  parameter logic [1:0][3:0] M = 8'h25;\n"
                       "  class D;\n"
                       "    logic [M[1]:0] m;\n"
                       "  endclass\n"
                       "  initial begin\n"
                       "    static C c = new;\n"
                       "    static D d = new;\n"
                       "    static pk::P p = new;\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", "
                       "$bits(c.a), $bits(c.b),\n"
                       "             $bits(c.i), $bits(C::s), $bits(C::L), "
                       "$bits(d.m),\n"
                       "             $bits(p.a));\n"
                       "    $display(\"%0d %0d %0d\", $bits(c.q), $bits(c.r), "
                       "$bits(c.v));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 11 12 12 7 3 7\n11 7 22\n");
}

TEST(MultidimensionalArraySimulation, SectionDeclarationsOrderTheirDimensions) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [3:0] [7:0] joe [1:10];\n"
                 "  bit [1:10] v1 [1:5];\n"
                 "  bit v2 [1:5] [1:10];\n"
                 "  bit [1:5] [1:10] v3;\n"
                 "  bit [1:5] [1:6] v4 [1:7] [1:8];\n"
                 "  typedef bit [1:5] bsix;\n"
                 "  bsix [1:10] v5;\n"
                 "  bit [7:0] [31:0] v7 [1:5] [1:10], v8 [0:255];\n"
                 "  initial begin\n"
                 "    joe[8] = 32'h01020304;\n"
                 "    joe[9] = joe[8] + 1;\n"
                 "    joe[6] = 32'hAABBCCDD;\n"
                 "    joe[7] = 0;\n"
                 "    joe[7][3:2] = joe[6][1:0];\n"
                 "    $display(\"%h %h\", joe[9], joe[7]);\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d\", $size(v1, 1), "
                 "$size(v1, 2),\n"
                 "             $size(v2, 1), $size(v2, 2), $size(v3, 1), "
                 "$size(v3, 2));\n"
                 "    $display(\"%0d %0d %0d %0d\", $size(v4, 1), $size(v4, "
                 "2), $size(v4, 3),\n"
                 "             $size(v4, 4));\n"
                 "    $display(\"%0d %0d\", $size(v5, 1), $size(v5, 2));\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d\", $size(v7, 1), "
                 "$size(v7, 2),\n"
                 "             $size(v7, 3), $size(v7, 4), $size(v8, 1), "
                 "$size(v8, 2));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "01020305 ccdd0000\n"
      "5 10 5 10 5 10\n"
      "7 8 5 6\n"
      "10 5\n"
      "5 10 8 32 256 8\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_UnpackedDimensionsStagedThroughATypedefFollowTheVariablesOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef bit [1:5] bsix;\n"
                       "typedef bsix mem_type [0:3];\n"
                       "mem_type cba [0:7];\n"
                       "package pk;\n"
                       "  mem_type pba [0:7];\n"
                       "endpackage\n"
                       "class K;\n"
                       "  mem_type kba [0:7];\n"
                       "endclass\n"
                       "module top;\n"
                       "  mem_type ba [0:7];\n"
                       "  K k;\n"
                       "  function automatic void f();\n"
                       "    mem_type lba [0:7];\n"
                       "    lba[7][3] = 5'h1f;\n"
                       "    $display(\"%0d %0d %0d %h\", $dimensions(lba), "
                       "$size(lba, 2), $size(lba[0]), lba[7][3]);\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    $display(\"%0d %0d %0d\", $dimensions(ba), "
                       "$size(ba, 2), $size(ba[0]));\n"
                       "    $display(\"%0d %0d %0d\", $dimensions(cba), "
                       "$size(cba, 2), $size(cba[0]));\n"
                       "    $display(\"%0d %0d %0d\", $dimensions(pk::pba), "
                       "$size(pk::pba, 2), $size(pk::pba[0]));\n"
                       "    $display(\"%0d %0d %0d\", $dimensions(k.kba), "
                       "$size(k.kba, 2), $size(k.kba[0]));\n"
                       "    f();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 4 4\n"
            "3 4 4\n"
            "3 4 4\n"
            "3 4 4\n"
            "3 4 4 1f\n");
}

TEST(MultidimensionalArraySimulation,
     SubarraysOfTwoDimensionsWholeArraysAndOtherShapesAreAssigned) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int A[2][3][4], B[2][3][4], C[5][4];\n"
          "  initial begin\n"
          "    foreach (A[i, j, k]) A[i][j][k] = -1;\n"
          "    foreach (B[i, j, k]) B[i][j][k] = i * 100 + j * 10 + k + 1;\n"
          "    foreach (C[i, j]) C[i][j] = 1000 + i * 10 + j;\n"
          "    A[1] = B[0];\n"
          "    $display(\"%0d %0d %0d %0d\", A[1][0][0], A[1][2][3], "
          "A[0][0][0],\n"
          "             A[0][2][3]);\n"
          "    A = B;\n"
          "    $display(\"%0d %0d %0d\", A[0][2][1], A[1][1][3], A == B);\n"
          "    A[0][1] = C[4];\n"
          "    $display(\"%0d %0d %0d %0d\", A[0][1][0], A[0][1][3], "
          "A[0][0][0],\n"
          "             A[0][2][0]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 24 -1 -1\n"
      "22 114 1\n"
      "1040 1043 1 21\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_SubarrayIsPassedToAnArrayFormal) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int B[2][3][4];\n"
          "  int D[3][4];\n"
          "  function automatic int sum(int x [3][4]);\n"
          "    int s = 0;\n"
          "    foreach (x[i, j]) s += x[i][j];\n"
          "    return s;\n"
          "  endfunction\n"
          "  initial begin\n"
          "    foreach (B[i, j, k]) B[i][j][k] = i * 100 + j * 10 + k + 1;\n"
          "    D = B[1];\n"
          "    $display(\"%0d %0d\", sum(D), sum(B[1]));\n"
          "  end\n"
          "endmodule\n",
          f),
      "1350 1350\n");
}

TEST(MultidimensionalArraySimulation,
     PackedArrayOfPackedStructSelectsInUnitPackageAndSubroutine) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "typedef logic [3:0] nib_t;\n"
          "ps_t [1:0] cv = 16'h1234;\n"
          "package pk;\n"
          "  ps_t [1:0] pv = 16'h1234;\n"
          "endpackage\n"
          "module top;\n"
          "  nib_t [1:0] n = 8'h6C;\n"
          "  function automatic void f();\n"
          "    ps_t [1:0] lv = 16'h1234;\n"
          "    $display(\"%h %h %h %h\", lv[1], lv[1].lo, lv[0].hi, lv[1:0]);\n"
          "    lv[0].hi = 4'hF;\n"
          "    lv[1] = 8'h56;\n"
          "    $display(\"%h\", lv);\n"
          "  endfunction\n"
          "  initial begin\n"
          "    $display(\"%h %h %h %h\", cv[1], cv[1].lo, cv[0].hi, cv[1:0]);\n"
          "    $display(\"%h %h %h %h\", pk::pv[1], pk::pv[1].lo, "
          "pk::pv[0].hi,\n"
          "             pk::pv[1:0]);\n"
          "    f();\n"
          "    cv[0].hi = 4'hF;\n"
          "    cv[1] = 8'h56;\n"
          "    pk::pv[0].hi = 4'hF;\n"
          "    pk::pv[1] = 8'h56;\n"
          "    $display(\"%h %h %h\", cv, pk::pv, n[1]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "12 2 3 1234\n"
      "12 2 3 1234\n"
      "12 2 3 1234\n"
      "56f4\n"
      "56f4 56f4 6\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_PackedArrayOfPackedStructSelectsInAModuleAndAClass) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "class K;\n"
          "  ps_t [1:0] kv = 16'h1234;\n"
          "endclass\n"
          "module top;\n"
          "  ps_t [1:0] v = 16'h1234;\n"
          "  K k;\n"
          "  initial begin\n"
          "    k = new;\n"
          "    $display(\"%h %h %h %h\", v[1], v[1].lo, v[0].hi, v[1:0]);\n"
          "    $display(\"%h %h %h %h\", k.kv[1], k.kv[1].lo, k.kv[0].hi, "
          "k.kv[1:0]);\n"
          "    v[0].hi = 4'hF;\n"
          "    v[1] = 8'h56;\n"
          "    k.kv[0].hi = 4'hF;\n"
          "    k.kv[1] = 8'h56;\n"
          "    $display(\"%h %h\", v, k.kv);\n"
          "  end\n"
          "endmodule\n",
          f),
      "12 2 3 1234\n"
      "12 2 3 1234\n"
      "56f4 56f4\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_PackedArrayMembersOfAnUnpackedStructAreWrittenThroughSelects) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "typedef struct { logic [1:0][3:0] q; ps_t [1:0] pa; } us_t;\n"
          "module top;\n"
          "  us_t s;\n"
          "  initial begin\n"
          "    s.q = 8'h6C;\n"
          "    s.q[0] = 4'h3;\n"
          "    s.pa = 16'h1234;\n"
          "    s.pa[1].lo = 4'h9;\n"
          "    s.pa[0] = 8'hAB;\n"
          "    $display(\"%h %h\", s.q, s.pa);\n"
          "  end\n"
          "endmodule\n",
          f),
      "63 19ab\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_FixedArrayOfVariableSizeArraysInBlocksAndSubroutines) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  typedef int q_t [$];\n"
          "  int dyn [];\n"
          "  function automatic void f();\n"
          "    int d1 [3][];\n"
          "    int d2 [3][$];\n"
          "    int d3 [3][string];\n"
          "    int d4 [3][int];\n"
          "    int d5 [3][$][2];\n"
          "    int d6 [3][][2];\n"
          "    q_t d7 [3];\n"
          "    var type(dyn) d8 [3];\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", $size(d1), "
          "$size(d2),\n"
          "             $size(d3), $size(d4), $size(d5), $size(d6), "
          "$size(d7),\n"
          "             $size(d8));\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", d1[0].size(), "
          "d2[0].size(),\n"
          "             d3[0].num(), d4[0].num(), d5[0].size(), d6[0].size(),\n"
          "             d7[0].size(), d8[0].size());\n"
          "    d2[1].push_back(7);\n"
          "    d3[2][\"k\"] = 4;\n"
          "    d4[1][9] = 5;\n"
          "    d7[2].push_back(6);\n"
          "    $display(\"%0d %0d %0d %0d\", d2[1][0], d3[2][\"k\"], d4[1][9], "
          "d7[2][0]);\n"
          "  endfunction\n"
          "  task automatic t();\n"
          "    int d2 [3][$];\n"
          "    int d3 [3][string];\n"
          "    $display(\"%0d %0d %0d\", $size(d2), $size(d3), d3[0].num());\n"
          "    d2[1].push_back(7);\n"
          "    d3[2][\"k\"] = 4;\n"
          "    $display(\"%0d %0d\", d2[1][0], d3[2][\"k\"]);\n"
          "  endtask\n"
          "  initial begin\n"
          "    int d1 [3][];\n"
          "    int d2 [3][$];\n"
          "    int d3 [3][string];\n"
          "    $display(\"%0d %0d %0d %0d\", $size(d1), $size(d2), $size(d3), "
          "d1[0].size());\n"
          "    d2[1].push_back(7);\n"
          "    d3[2][\"k\"] = 4;\n"
          "    $display(\"%0d %0d\", d2[1][0], d3[2][\"k\"]);\n"
          "    f();\n"
          "    t();\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 3 3 0\n"
      "7 4\n"
      "3 3 3 3 3 3 3 3\n"
      "0 0 0 0 0 0 0 0\n"
      "7 4 5 6\n"
      "3 3 0\n"
      "7 4\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_ModuleArraysOfAssociativeArraysKeepTheirEntries) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int ma [2][string];\n"
                       "  int mi [3][int];\n"
                       "  int dm [][string];\n"
                       "  int da [][int];\n"
                       "  initial begin\n"
                       "    ma[1][\"k\"] = 4;\n"
                       "    $display(\"%0d %0d %0d\", ma[1][\"k\"], "
                       "ma[1].num(), ma[1].exists(\"k\"));\n"
                       "    mi[1][9] = 5;\n"
                       "    $display(\"%0d %0d\", mi[1][9], mi[1].num());\n"
                       "    dm = new[2];\n"
                       "    dm[1][\"k\"] = 4;\n"
                       "    da = new[2];\n"
                       "    da[1][9] = 5;\n"
                       "    $display(\"%0d %0d\", dm[1][\"k\"], da[1][9]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 1 1\n"
            "5 1\n"
            "4 5\n");
}

TEST(MultidimensionalArraySimulation,
     DISABLED_SubarraysAreComparedElementByElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int A[2][3][4], B[2][3][4];\n"
          "  int X[3][4], Y[3][4];\n"
          "  initial begin\n"
          "    foreach (B[i, j, k]) B[i][j][k] = i * 100 + j * 10 + k + 1;\n"
          "    A = B;\n"
          "    foreach (X[i, j]) X[i][j] = i + j;\n"
          "    Y = X;\n"
          "    Y[2][3] = 99;\n"
          "    $display(\"%0d %0d %0d %0d\", A[1] == B[1], A[0] == B[1],\n"
          "             A[0][1] == B[1][1], A[0][1][2] == B[1][1][2]);\n"
          "    $display(\"%0d %0d %0d\", X == Y, A == B, A[0] != B[1]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 0 0 0\n0 1 1\n");
}

}  // namespace
