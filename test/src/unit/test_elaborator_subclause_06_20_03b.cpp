#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kRestricted =
    "may prefix the class scope resolution operator only within a typedef "
    "declaration, the type operator, or a type parameter assignment";
constexpr std::string_view kNotAClass =
    "used as a class scope resolution prefix does not resolve to a class";

::testing::AssertionResult NoErrorAt(const std::vector<Diagnostic>& diags,
                                     uint32_t line) {
  ::testing::AssertionResult failure = ::testing::AssertionFailure();
  bool any = false;
  for (const auto& diag : diags) {
    if (diag.severity != DiagSeverity::kError || diag.loc.line != line)
      continue;
    any = true;
    failure << "\n  error at line " << line << " under §" << diag.subclause
            << ": " << diag.message;
  }
  if (!any) return ::testing::AssertionSuccess();
  return failure;
}

void ExpectReportedOnlyOn(const ElabFixture& f, std::string_view message,
                          std::initializer_list<uint32_t> reported,
                          std::initializer_list<uint32_t> accepted) {
  for (uint32_t line : reported) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "6.20.3"))
        << line;
  }
  for (uint32_t line : accepted) {
    EXPECT_TRUE(NoErrorAt(f.diag.Diagnostics(), line)) << line;
  }
}

TEST(TypeParameterElab, ValueSelectedThroughAClassBoundTypeParamIsAccepted) {
  ElabFixture f;
  Elaborate(
      "class K;\n"
      "  static int n = 1;\n"
      "  localparam int P = 2;\n"
      "  static function int sf(); return 3; endfunction\n"
      "  typedef byte kt;\n"
      "  localparam type KL = byte;\n"
      "  class KN; static int n = 4; endclass\n"
      "endclass\n"
      "package pk;\n"
      "  localparam type PT = K;\n"
      "  int pv = PT::n;\n"
      "  function automatic int pf(); return PT::P + PT::sf(); endfunction\n"
      "endpackage\n"
      "localparam type UT = K;\n"
      "int uv = UT::n;\n"
      "function automatic int uf(); return UT::P + UT::sf(); endfunction\n"
      "class W #(type T = K);\n"
      "  localparam type BT = K;\n"
      "  localparam type BT2 = T;\n"
      "  int y = T::n;\n"
      "  rand int r;\n"
      "  constraint c { r < T::P; }\n"
      "  function int f(); return T::sf() + BT::n; endfunction\n"
      "  task t(); y = T::P; endtask\n"
      "  function int g(); return pk::PT::n + $unit::UT::P + K::n + "
      "$bits(K::kt); endfunction\n"
      "  function int h(); return BT2::n; endfunction\n"
      "endclass\n"
      "class W2 #(int N = 1, type T = K);\n"
      "endclass\n"
      "interface ifc #(type T = K);\n"
      "  int iv = T::n;\n"
      "  initial iv = T::P;\n"
      "endinterface\n"
      "program prg #(type T = K);\n"
      "  int gv;\n"
      "  initial gv = T::sf();\n"
      "endprogram\n"
      "module top #(type T = K);\n"
      "  localparam type MT = K;\n"
      "  int a = T::n;\n"
      "  wire [31:0] w;\n"
      "  assign w = T::P;\n"
      "  int b;\n"
      "  initial b = MT::sf();\n"
      "  always @(a) b = T::n;\n"
      "  function automatic int mf(); return T::P; endfunction\n"
      "  task automatic mt(); b = T::sf(); endtask\n"
      "  if (1) begin : g\n"
      "    localparam type GT = K;\n"
      "    int gw = GT::n;\n"
      "    initial b = T::P + GT::sf();\n"
      "  end\n"
      "  initial begin\n"
      "    localparam type LT = K;\n"
      "    b = LT::n;\n"
      "    begin typedef K LU; b = LU::P; end\n"
      "  end\n"
      "  initial b = pk::PT::n;\n"
      "  initial b = $unit::UT::P;\n"
      "  initial b = W#()::T::sf();\n"
      "  initial b = W#(K)::T::n;\n"
      "  initial b = W#(.T(K))::T::n;\n"
      "  initial b = W#()::BT::n;\n"
      "  initial b = W2#(3, K)::T::n;\n"
      "  initial b = W2#(.N(3))::T::n;\n"
      "  initial b = K::KN::n;\n"
      "  initial b = $unit::K::n;\n"
      "  initial b = $bits(K::kt) + K::kt'(5);\n"
      "  initial b = $unit::W#()::T::n + $unit::W2#(3, K)::T::n;\n"
      "  W wd;\n"
      "  W2 w2;\n"
      "  ifc u_i();\n"
      "  prg u_p();\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass, {},
                       {11, 12, 15, 16, 20, 22, 23, 24, 25, 26, 31, 32, 36,
                        40, 42, 44, 45, 46, 47, 50, 51, 55, 56, 58, 59, 60,
                        61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73});
}

TEST(TypeParameterElab, ValueSelectedThroughANonClassTypeParamIsNotAClass) {
  ElabFixture f;
  Elaborate(
      "class K;\n"
      "  static int n = 1;\n"
      "endclass\n"
      "typedef struct { int a; } st;\n"
      "package pk;\n"
      "  localparam type PT = int;\n"
      "  int pv = PT::n;\n"
      "  function automatic int pf(); return PT::P; endfunction\n"
      "  localparam type PT2 = PT;\n"
      "  int pw = PT2::n;\n"
      "  localparam type PS = st;\n"
      "  int ps = PS::n;\n"
      "endpackage\n"
      "localparam type UT = int;\n"
      "int uv = UT::n;\n"
      "function automatic int uf(); return UT::sf(); endfunction\n"
      "class W #(type T = int);\n"
      "  int y = T::n;\n"
      "endclass\n"
      "class W2 #(int N = 1, type T = int);\n"
      "  int y = T::n;\n"
      "endclass\n"
      "class V #(type T = int);\n"
      "  rand int r;\n"
      "  constraint c { r < T::n; }\n"
      "endclass\n"
      "class X #(type T = int);\n"
      "  localparam type XP = pk::PT;\n"
      "  function int f(); return K::n + T::sf(); endfunction\n"
      "endclass\n"
      "class Y #(type T = int);\n"
      "  task t(); int z; z = T::n; z = 0; endtask\n"
      "endclass\n"
      "class Q #(type T = int);\n"
      "  localparam type QB = T;\n"
      "  function int f(); return QB::n; endfunction\n"
      "endclass\n"
      "class N #(type T = int);\n"
      "  function int f(); if (1) begin return T::n; end return 0; "
      "endfunction\n"
      "endclass\n"
      "class TR #(type T = int);\n"
      "  typedef type(T::n) tn;\n"
      "endclass\n"
      "typedef K UU;\n"
      "class U #(type UU = int);\n"
      "  function int f(); return $unit::UU::n; endfunction\n"
      "endclass\n"
      "class Z;\n"
      "  localparam type BZ = int;\n"
      "  function int f(); return BZ::n; endfunction\n"
      "endclass\n"
      "interface ifc #(type T = int);\n"
      "  int iv = T::n;\n"
      "  initial iv = T::P;\n"
      "endinterface\n"
      "interface ifs #(type T = st);\n"
      "  int sv = T::n;\n"
      "  initial sv = $bits(T::n);\n"
      "endinterface\n"
      "program prg #(type T = int);\n"
      "  int gv;\n"
      "  initial gv = T::sf();\n"
      "endprogram\n"
      "module top #(type T = int);\n"
      "  localparam type MT = int;\n"
      "  int a = T::n;\n"
      "  wire [31:0] w;\n"
      "  assign w = T::P;\n"
      "  int b;\n"
      "  initial b = MT::sf();\n"
      "  always @(a) b = T::n;\n"
      "  function automatic int mf(); return T::P; endfunction\n"
      "  task automatic mt(); b = T::sf(); endtask\n"
      "  initial b = $bits(T::n);\n"
      "  if (1) begin : g\n"
      "    localparam type GT = int;\n"
      "    int gw = GT::n;\n"
      "    initial b = GT::sf();\n"
      "    initial b = T::P;\n"
      "  end\n"
      "  initial begin\n"
      "    localparam type LT = int;\n"
      "    b = LT::n;\n"
      "    begin localparam type LS = st; b = $bits(LS::n); end\n"
      "  end\n"
      "  initial b = pk::PT::n;\n"
      "  initial b = $unit::UT::P;\n"
      "  initial b = W#(int)::T::n;\n"
      "  initial b = W#(.T(int))::T::n;\n"
      "  initial b = W#(int unsigned)::T::n;\n"
      "  initial b = W2#(3, int)::T::n;\n"
      "  initial b = W2#(.N(3))::T::n;\n"
      "  initial b = Z::BZ::n;\n"
      "  initial b = $unit::W#()::T::n;\n"
      "  initial b = $bits($unit::W#()::T::inner);\n"
      "  initial b = $unit::W2#(3, int)::T::n;\n"
      "  W wd;\n"
      "  W #(K) wk;\n"
      "  W2 w2;\n"
      "  V #(int) vi;\n"
      "  X #(int) xi;\n"
      "  Y #(int) yi;\n"
      "  Q #(int) qi;\n"
      "  Q #(K) qk;\n"
      "  N #(int) ni;\n"
      "  N #(K) nk;\n"
      "  TR #(int) tr;\n"
      "  TR #(K) tk;\n"
      "  U #(int) ui;\n"
      "  Z zd;\n"
      "  ifc u_i();\n"
      "  ifs u_s();\n"
      "  prg u_p();\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(
      f, kNotAClass,
      {7,  8,  10, 12, 15, 16, 50, 53,  54,  57,  58,  62,  66, 68, 70,
       71, 72, 73, 74, 77, 78, 79, 83,  84,  86,  87,  88,  89, 90, 91,
       92, 93, 94, 95, 96, 97, 99, 100, 101, 102, 103, 105, 107},
      {28, 46, 98, 104, 106, 108, 109});
}

TEST(TypeParameterElab,
     TypeSelectedThroughAModuleTypeParamOutsideTheThreePlacesIsRestricted) {
  ElabFixture f;
  Elaborate(
      "class K;\n"
      "  typedef byte inner; static int n = 1; localparam int P = 4; class nk; "
      "endclass\n"
      "endclass\n"
      "interface ifc #(type T = K);\n"
      "  T::inner iv;\n"
      "  typedef T::inner it;\n"
      "  it iw;\n"
      "endinterface\n"
      "program prg #(type T = K);\n"
      "  T::inner gv;\n"
      "  typedef T::inner gt;\n"
      "  gt gw;\n"
      "endprogram\n"
      "module mp #(type T = K) (input T::inner pin);\n"
      "endmodule\n"
      "module mq #(type T = K) (input var type(T::inner) qin);\n"
      "endmodule\n"
      "module top #(type T = K);\n"
      "  typedef T::inner mt;\n"
      "  wire T::inner w;\n"
      "  wire mt w2;\n"
      "  parameter T::inner VP = 0;\n"
      "  localparam T::inner LP = 0;\n"
      "  localparam mt LQ = 0;\n"
      "  struct packed { T::inner m; } s;\n"
      "  struct packed { mt m; } s2;\n"
      "  int b;\n"
      "  function automatic T::inner mf(); return 0; endfunction\n"
      "  function automatic int mg(T::inner fa); return fa; endfunction\n"
      "  function automatic int mh(); T::inner fl; fl = 0; return fl; "
      "endfunction\n"
      "  function automatic mt mi(mt fa); mt fl; fl = fa; return fl; "
      "endfunction\n"
      "  task automatic mtk(T::inner ta); endtask\n"
      "  task automatic mtl(mt ta); endtask\n"
      "  initial begin T::inner bl; bl = 0; b = bl; end\n"
      "  initial begin mt bl; bl = 0; b = bl; end\n"
      "  initial b = T::inner'(5);\n"
      "  initial b = mt'(5);\n"
      "  initial b = $bits(T::inner);\n"
      "  initial b = $bits(mt);\n"
      "  if (1) begin : g\n"
      "    localparam type GT = K;\n"
      "    T::inner gx;\n"
      "    GT::inner gy;\n"
      "    typedef GT::inner gt;\n"
      "    gt gz;\n"
      "  end\n"
      "  mp u_p();\n"
      "  mq u_q();\n"
      "  ifc u_i();\n"
      "  prg u_g();\n"
      "  initial $display($typename(T::inner));\n"
      "  initial b = $left(T::inner);\n"
      "  initial $display($typename(T::nk));\n"
      "  initial $display($typename(mt), $left(mt));\n"
      "  initial b = $bits(T::n);\n"
      "  initial b = $bits(K::inner) + K::inner'(5) + $unit::K::inner'(5);\n"
      "  initial b = T::P'(5);\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kRestricted,
                       {5, 10, 14, 20, 22, 23, 25, 28, 29, 30, 32, 34, 36, 38,
                        42, 43, 51, 52, 53},
                       {6,  7,  11, 12, 16, 19, 21, 24, 26, 31, 33,
                        35, 37, 39, 44, 45, 47, 48, 54, 55, 56, 57});
}

TEST(
    TypeParameterElab,
    TypeSelectedThroughAUnitOrClassTypeParamOutsideTheThreePlacesIsRestricted) {
  ElabFixture f;
  Elaborate(
      "class K;\n"
      "  typedef byte inner; localparam int P = 2; class KN; typedef byte "
      "inner; endclass\n"
      "endclass\n"
      "package pk;\n"
      "  localparam type PT = K;\n"
      "  PT::inner px;\n"
      "  function automatic PT::inner pf(); return 0; endfunction\n"
      "  typedef PT::inner pt;\n"
      "  pt py;\n"
      "  function automatic pt pg(); return 0; endfunction\n"
      "endpackage\n"
      "localparam type UT = K;\n"
      "UT::inner ux;\n"
      "function automatic UT::inner uf(); return 0; endfunction\n"
      "typedef UT::inner ut;\n"
      "ut uy;\n"
      "function automatic ut ug(); return 0; endfunction\n"
      "class W #(type T = K);\n"
      "  localparam type BT = K; typedef pk::PT::inner wp;\n"
      "  typedef T::inner wt;\n"
      "  function T::inner f(); return 0; endfunction\n"
      "  function int g(T::inner a); return a; endfunction\n"
      "  function int h(); BT::inner l; l = 0; return l; endfunction\n"
      "  function int i(); return T::inner'(5); endfunction\n"
      "  function int j(); return $bits(T::inner); endfunction\n"
      "  function wt k(wt a); wt l; l = a; return l; endfunction\n"
      "  function int m(); return wt'(5) + $bits(wt); endfunction\n"
      "  function int p(); return T::P'(5) + BT::P'(5); endfunction\n"
      "endclass\n"
      "module top;\n"
      "  pk::PT::inner ox;\n"
      "  W#()::T::inner oy;\n"
      "  W#()::BT::inner ow;\n"
      "  typedef pk::PT::inner ot;\n"
      "  ot oz;\n"
      "  K::KN::inner on;\n"
      "  W wd;\n"
      "  int b;\n"
      "  initial b = pk::PT::inner'(5);\n"
      "  initial b = $bits(pk::PT::inner);\n"
      "  initial b = W#()::T::inner'(5);\n"
      "  initial b = $bits($unit::UT::inner);\n"
      "  initial b = $unit::UT::inner'(5);\n"
      "  $unit::UT::inner ux2;\n"
      "  initial b = $bits($unit::W#()::T::inner);\n"
      "  initial b = $unit::W#()::T::inner'(5);\n"
      "  initial b = pk::PT::P'(5) + $unit::UT::P'(5) + W#()::T::P'(5);\n"
      "  initial b = $bits($unit::W#()::T::P) + $unit::W#()::T::P'(5);\n"
      "  initial b = $bits(pk::PT::P) + $bits($unit::UT::P);\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(
      f, kRestricted, {6,  7,  13, 14, 21, 22, 23, 24, 25, 31,
                       32, 33, 39, 40, 41, 42, 43, 44, 45, 46},
      {8, 9, 10, 15, 16, 17, 19, 20, 26, 27, 28, 34, 35, 36, 37, 47, 48, 49});
}

TEST(TypeParameterElab, ClassBoundPrefixInTheThreePlacesIsAccepted) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; static int n = 1; endclass\n"
      "class Y #(int P = 0); endclass\n"
      "package pk;\n"
      "  localparam type PT = K;\n"
      "endpackage\n"
      "localparam type UT = K;\n"
      "class W #(type T = K); endclass\n"
      "package q;\n"
      "  typedef pk::PT::inner q1;\n"
      "  var type($unit::UT::inner) q2;\n"
      "  localparam type Q3 = W#()::T::inner;\n"
      "  localparam int Q4 = $bits(type(pk::PT::inner));\n"
      "endpackage\n"
      "typedef pk::PT::inner u1;\n"
      "var type(W#(K)::T::inner) u2;\n"
      "localparam type U3 = $unit::UT::inner;\n"
      "localparam int U4 = $bits(type(pk::PT::inner));\n"
      "checker ck;\n"
      "  typedef pk::PT::inner k1;\n"
      "  var type($unit::UT::inner) k2;\n"
      "  int k3 = $bits(type(pk::PT::inner));\n"
      "endchecker\n"
      "class C;\n"
      "  localparam type BZ = K;\n"
      "  typedef pk::PT::inner c1;\n"
      "  var type($unit::UT::inner) c2;\n"
      "  localparam type C3 = W#(.T(K))::T::inner;\n"
      "  typedef BZ::inner c4;\n"
      "  localparam type C5 = BZ::inner;\n"
      "  var type(BZ::inner) c6;\n"
      "  function int f(); typedef pk::PT::inner fl; return 0; endfunction\n"
      "  int c7 = $bits(type(BZ::inner));\n"
      "  function int g(); return $bits(type(1 + BZ::n)); endfunction\n"
      "endclass\n"
      "class WT #(type T = int);\n"
      "  var type(T::inner) p;\n"
      "endclass\n"
      "class D #(type U = K, type V = U::inner);\n"
      "endclass\n"
      "class E #(type V = pk::PT::inner); endclass\n"
      "interface ifc #(type U = K, type V = U::inner);\n"
      "endinterface\n"
      "module mpo #(type V = pk::PT::inner);\n"
      "endmodule\n"
      "module mpd #(type V = pk::PT::inner);\n"
      "endmodule\n"
      "module top;\n"
      "  typedef pk::PT::inner t1;\n"
      "  var type($unit::UT::inner) t2;\n"
      "  localparam type T3 = W#(K)::T::inner;\n"
      "  if (1) begin : g\n"
      "    typedef W#()::T::inner g1;\n"
      "  end\n"
      "  initial begin typedef pk::PT::inner b1; b1 v; end\n"
      "  initial begin var type($unit::UT::inner) b2; end\n"
      "  function automatic int mf(); localparam type F1 = $unit::UT::inner; "
      "return 0; endfunction\n"
      "  localparam type LB = K;\n"
      "  localparam int TQ = $bits(type(LB::inner));\n"
      "  int tn = $bits(type(pk::PT::inner));\n"
      "  initial tn = $bits(type($unit::UT::inner));\n"
      "  initial tn = $bits(type(1 + LB::n));\n"
      "  typedef Y #($bits(type(LB::inner))) ty;\n"
      "  localparam type TY = Y #($bits(type(W#()::T::inner)));\n"
      "  if (1) begin : g2\n"
      "    localparam int GQ = $bits(type(LB::inner));\n"
      "  end\n"
      "  C c;\n"
      "  WT #(K) wt;\n"
      "  D dd;\n"
      "  ifc u_i();\n"
      "  mpo u_o();\n"
      "  mpd #(.V(byte)) u_d();\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass, {},
                       {9,  10, 11, 12, 14, 15, 16, 17, 19, 20, 21, 25, 26, 27,
                        28, 29, 30, 31, 32, 33, 40, 41, 43, 45, 48, 49, 50, 52,
                        54, 55, 56, 58, 59, 60, 61, 62, 63, 65, 68, 69, 72});
}

TEST(TypeParameterElab, NonClassPrefixInTheThreePlacesIsNotAClass) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; static int n = 1; endclass\n"
      "class Y #(int P = 0); endclass\n"
      "package pk;\n"
      "  localparam type PT = int;\n"
      "endpackage\n"
      "localparam type UT = int;\n"
      "class W #(type T = int); endclass\n"
      "package q;\n"
      "  typedef pk::PT::inner q1;\n"
      "  var type($unit::UT::inner) q2;\n"
      "  localparam type Q3 = W#()::T::inner;\n"
      "  localparam int Q4 = $bits(type(pk::PT::inner));\n"
      "endpackage\n"
      "typedef pk::PT::inner u1;\n"
      "var type(W#(int)::T::inner) u2;\n"
      "localparam type U3 = $unit::UT::inner;\n"
      "localparam int U4 = $bits(type(pk::PT::inner));\n"
      "checker ck;\n"
      "  typedef pk::PT::inner k1;\n"
      "  var type($unit::UT::inner) k2;\n"
      "  int k3 = $bits(type(pk::PT::inner));\n"
      "endchecker\n"
      "class C;\n"
      "  localparam type BZ = int;\n"
      "  typedef pk::PT::inner c1;\n"
      "  var type($unit::UT::inner) c2;\n"
      "  localparam type C3 = W#(.T(int))::T::inner;\n"
      "  typedef BZ::inner c4;\n"
      "  localparam type C5 = BZ::inner;\n"
      "  var type(BZ::inner) c6;\n"
      "  function int f(); typedef pk::PT::inner fl; return 0; endfunction\n"
      "  int c7 = $bits(type(BZ::inner));\n"
      "  function int g(); return $bits(type(1 + BZ::n)); endfunction\n"
      "endclass\n"
      "class WT #(type T = int);\n"
      "  var type(T::inner) p;\n"
      "endclass\n"
      "class D #(type U = int, type V = U::inner);\n"
      "endclass\n"
      "class E #(type V = pk::PT::inner); endclass\n"
      "interface ifc #(type U = int, type V = U::inner);\n"
      "endinterface\n"
      "module mpo #(type V = pk::PT::inner);\n"
      "endmodule\n"
      "module mpd #(type V = pk::PT::inner);\n"
      "endmodule\n"
      "module top;\n"
      "  typedef pk::PT::inner t1;\n"
      "  var type($unit::UT::inner) t2;\n"
      "  localparam type T3 = W#(int)::T::inner;\n"
      "  if (1) begin : g\n"
      "    typedef W#()::T::inner g1;\n"
      "  end\n"
      "  initial begin typedef pk::PT::inner b1; b1 v; end\n"
      "  initial begin var type($unit::UT::inner) b2; end\n"
      "  function automatic int mf(); localparam type F1 = $unit::UT::inner; "
      "return 0; endfunction\n"
      "  localparam type LB = int;\n"
      "  localparam int TQ = $bits(type(LB::inner));\n"
      "  int tn = $bits(type(pk::PT::inner));\n"
      "  initial tn = $bits(type($unit::UT::inner));\n"
      "  initial tn = $bits(type(1 + LB::n));\n"
      "  typedef Y #($bits(type(LB::inner))) ty;\n"
      "  localparam type TY = Y #($bits(type(W#()::T::inner)));\n"
      "  if (1) begin : g2\n"
      "    localparam int GQ = $bits(type(LB::inner));\n"
      "  end\n"
      "  C c;\n"
      "  WT #(int) wt;\n"
      "  D dd;\n"
      "  ifc u_i();\n"
      "  mpo u_o();\n"
      "  mpd #(.V(byte)) u_d();\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass,
                       {9,  10, 11, 12, 14, 15, 16, 17, 19, 20, 21, 25, 26,
                        27, 28, 29, 30, 31, 32, 33, 40, 41, 43, 48, 49, 50,
                        52, 54, 55, 56, 58, 59, 60, 61, 62, 63, 65, 68, 69},
                       {45, 72});
}

TEST(TypeParameterElab,
     ValueSelectedThroughAScopedBindingIsJudgedByTheTypeItNames) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; static int n = 1; endclass\n"
      "package pk;\n"
      "  class K; typedef byte inner; static int n = 1; endclass\n"
      "  typedef int I;\n"
      "  typedef K J;\n"
      "  localparam type PT = int;\n"
      "  localparam type PK = K;\n"
      "endpackage\n"
      "typedef int UI;\n"
      "localparam type UT = int;\n"
      "localparam type C1 = pk::I;\n"
      "int cv = C1::n;\n"
      "localparam type C2 = pk::K;\n"
      "int cw = C2::n;\n"
      "package pq;\n"
      "  localparam type Q1 = pk::PT;\n"
      "  int qv = Q1::n;\n"
      "  localparam type Q2 = pk::J;\n"
      "  int qw = Q2::n;\n"
      "endpackage\n"
      "class C;\n"
      "  localparam type B1 = $unit::UI;\n"
      "  localparam type B2 = $unit::K;\n"
      "  function int f(); return B1::n; endfunction\n"
      "  function int g(); return B2::n; endfunction\n"
      "endclass\n"
      "module mm #(type T = pk::I);\n"
      "  int a = T::n;\n"
      "endmodule\n"
      "module mk #(type T = pk::K);\n"
      "  int a = T::n;\n"
      "endmodule\n"
      "module top;\n"
      "  localparam type L1 = pk::K;\n"
      "  localparam type L2 = pk::I;\n"
      "  localparam type L3 = pk::PT;\n"
      "  localparam type L4 = $unit::K;\n"
      "  localparam type L5 = $unit::UI;\n"
      "  localparam type L6 = $unit::UT;\n"
      "  localparam type L7 = pk::J;\n"
      "  localparam type L8 = pk::PK;\n"
      "  int b;\n"
      "  initial b = L1::n;\n"
      "  initial b = L2::n;\n"
      "  initial b = L3::n;\n"
      "  initial b = L4::n;\n"
      "  initial b = L5::n;\n"
      "  initial b = L6::n;\n"
      "  initial b = L7::n;\n"
      "  initial b = L8::n;\n"
      "  initial begin localparam type BL = pk::I; b = BL::n; end\n"
      "  initial begin localparam type BK = pk::K; b = BK::n; end\n"
      "  C c;\n"
      "  mm u_m();\n"
      "  mk u_k();\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass, {12, 17, 24, 28, 44, 45, 47, 48, 51},
                       {14, 19, 25, 31, 43, 46, 49, 50, 52, 53, 54, 55});
}

TEST(TypeParameterElab,
     TypeSelectedThroughAScopedBindingOutsideTheThreePlacesIsRestricted) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; static int n = 1; endclass\n"
      "class KS; static int inner = 1; endclass\n"
      "package pk;\n"
      "  class KS; typedef byte inner; endclass\n"
      "endpackage\n"
      "class W #(type T = K); endclass\n"
      "localparam type C1 = pk::KS;\n"
      "int cv = $bits(C1::inner);\n"
      "module top;\n"
      "  localparam type L1 = pk::KS;\n"
      "  localparam type L2 = $unit::KS;\n"
      "  localparam type L3 = $unit::K;\n"
      "  typedef K KT;\n"
      "  int b;\n"
      "  initial b = $bits(L1::inner);\n"
      "  initial b = L1::inner'(5);\n"
      "  initial b = $bits(L2::inner);\n"
      "  initial b = $bits(L3::inner);\n"
      "  initial b = $bits(KT::inner) + KT::inner'(5);\n"
      "  initial begin localparam type BL = pk::KS; b = $bits(BL::inner); end\n"
      "  initial begin localparam type BS = KS; b = $bits(BS::inner); end\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kRestricted, {8, 15, 16, 18, 20}, {17, 19, 21});
}

TEST(TypeParameterElab,
     TypeSelectedThroughAClassTypeParamIsJudgedPerSpecialization) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; static int n = 1; localparam int P = 2; "
      "endclass\n"
      "class KV; static int inner = 1; endclass\n"
      "class X #(type V = int); endclass\n"
      "class Y #(int P = 0); endclass\n"
      "class W #(type T);\n"
      "  X #(T::inner) p;\n"
      "  X #(.V(T::inner)) p2;\n"
      "  Y #(T::P) q;\n"
      "  X #(int) pi;\n"
      "  X #($unit::K::inner) pu;\n"
      "  typedef X #(T::inner) wt;\n"
      "  function void f2(X #(T::inner) a); endfunction\n"
      "  localparam type WB = T;\n"
      "  int a = $bits(T::inner);\n"
      "  int c = T::n + $bits(T::n);\n"
      "  function int f(); return T::inner'(5); endfunction\n"
      "  function int g(); if (c > 0) return $bits(WB::inner); return 0; "
      "endfunction\n"
      "  function int h(); return $bits(K::inner) + $bits(c) + "
      "$bits($unit::K::inner) + $bits(type(T::inner)) + byte'(c); endfunction\n"
      "  rand int r;\n"
      "  constraint cs { r < $bits(T::inner); }\n"
      "endclass\n"
      "class V #(type T = KV);\n"
      "  int a = $bits(T::inner);\n"
      "  int c = $bits(T::n);\n"
      "endclass\n"
      "class D2 #(type T = K) extends X #(T::inner); endclass\n"
      "class D3 #(type T = K) extends Y #(T::P); endclass\n"
      "interface class IC #(type V = int); endclass\n"
      "interface class IE #(type T = K) extends IC #(T::inner); endclass\n"
      "interface class IC2 #(type V = int); endclass\n"
      "interface class IE2 #(type T = K) extends IC2 #(int), IC #(T::inner); "
      "endclass\n"
      "class D4 #(type T) implements IC #(T::inner); endclass\n"
      "class D5 #(type T) extends X #(T::inner); endclass\n"
      "class B6; function new(int a); endfunction endclass\n"
      "class D6 #(type T = K) extends B6(T::n); endclass\n"
      "module top;\n"
      "  W #(K) wk;\n"
      "  W #(KV) wv;\n"
      "  D4 #(K) d4;\n"
      "  D5 #(K) d5;\n"
      "  D6 d6;\n"
      "  V vd;\n"
      "  V #(K) vk;\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(
      f, kRestricted, {6, 7, 12, 14, 16, 17, 20, 23, 26, 29, 31, 32, 33},
      {8, 9, 10, 11, 15, 18, 24, 27, 35, 37, 38, 39, 40, 41, 42, 43});
}

TEST(
    TypeParameterElab,
    TypeSelectedThroughAClassBoundTypeParamInAParameterValueAssignmentIsRestricted) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; localparam int P = 2; endclass\n"
      "class X #(type V = int); V v; endclass\n"
      "class Y #(int P = 0); endclass\n"
      "class W #(type T = K); endclass\n"
      "class WY #(type T = K);\n"
      "  Y #(T::P) q;\n"
      "  typedef X #(T::inner) xt;\n"
      "endclass\n"
      "class B7; function new(int a); endfunction endclass\n"
      "class WB #(type T = K) extends B7(T::n); endclass\n"
      "class WF #(type T = K);\n"
      "  function void f(Y #(T::P) a); endfunction\n"
      "endclass\n"
      "module m #(type V = int, int P = 0); endmodule\n"
      "interface ifc #(type V = int); endinterface\n"
      "program prg #(type V = int); endprogram\n"
      "package pq;\n"
      "  localparam type QT = K;\n"
      "  X #(QT::inner) qx;\n"
      "  typedef X #(QT::inner) qt;\n"
      "endpackage\n"
      "localparam type UT = K;\n"
      "X #(UT::inner) ux;\n"
      "typedef X #(UT::inner) ut;\n"
      "interface ifo #(type T = K);\n"
      "  X #(T::inner) ix;\n"
      "  ifc #(.V(T::inner)) sub();\n"
      "endinterface\n"
      "module top #(type T = K);\n"
      "  localparam type LT = K;\n"
      "  typedef T::inner ti;\n"
      "  X #(T::inner) x1;\n"
      "  X #(.V(T::inner)) x2;\n"
      "  X #(ti) x3;\n"
      "  X #(X #(T::inner)) x4;\n"
      "  X #(LT::inner) x5;\n"
      "  X #($unit::UT::inner) x6;\n"
      "  X #(W#()::T::inner) x7;\n"
      "  Y #(T::P) y1;\n"
      "  Y #(.P(LT::P)) y2;\n"
      "  Y #(K::P) y3;\n"
      "  Y #($bits(T::inner)) y5;\n"
      "  typedef Y #(1 + T::P) yp;\n"
      "  typedef K KT;\n"
      "  X #(KT::inner) x8;\n"
      "  W #(T::inner)::T z1;\n"
      "  virtual ifc #(.V(T::inner)) vi;\n"
      "  m #(.V(), .P(T::P)) u6();\n"
      "  struct { X #(T::inner) h; } s1;\n"
      "  typedef X #(T::inner) xt;\n"
      "  localparam type XL = X #(T::inner);\n"
      "  var type(X #(T::inner)) xv;\n"
      "  m #(.V(T::inner)) u1();\n"
      "  m #(T::inner, T::P) u2();\n"
      "  m #(.V(ti), .P(T::P)) u3();\n"
      "  m #(.V(LT::inner)) u4();\n"
      "  m #(.V($unit::UT::inner)) u5();\n"
      "  ifc #(.V(T::inner)) i1();\n"
      "  prg #(.V(T::inner)) p1();\n"
      "  ifo io();\n"
      "  WY #(K) wy;\n"
      "  WB #(K) wb;\n"
      "  WF #(K) wf;\n"
      "  if (1) begin : g\n"
      "    X #(T::inner) gx;\n"
      "    m #(.V(T::inner)) gu();\n"
      "  end\n"
      "  initial begin X #(T::inner) bx; end\n"
      "  function automatic void mf(X #(T::inner) a); endfunction\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(
      f, kRestricted, {19, 23, 26, 27, 32, 33, 35, 36, 37, 38, 42, 46,
                       47, 49, 53, 54, 56, 57, 58, 59, 65, 66, 68, 69},
      {20, 24, 31, 34, 39, 40, 41, 43, 45, 48, 50, 51, 52, 55, 60, 61, 62, 63});
}

TEST(TypeParameterElab,
     SelectionThroughANonClassTypeParamInAParameterValueAssignmentIsNotAClass) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; localparam int P = 2; endclass\n"
      "class X #(type V = int); V v; endclass\n"
      "class Y #(int P = 0); endclass\n"
      "class W #(type T = int); endclass\n"
      "class WY #(type T = K);\n"
      "  Y #(T::P) q;\n"
      "  typedef X #(T::inner) xt;\n"
      "endclass\n"
      "class B7; function new(int a); endfunction endclass\n"
      "class WB #(type T = K) extends B7(T::n); endclass\n"
      "class WF #(type T = K);\n"
      "  function void f(Y #(T::P) a); endfunction\n"
      "endclass\n"
      "module m #(type V = int, int P = 0); endmodule\n"
      "interface ifc #(type V = int); endinterface\n"
      "program prg #(type V = int); endprogram\n"
      "package pq;\n"
      "  localparam type QT = int;\n"
      "  X #(QT::inner) qx;\n"
      "  typedef X #(QT::inner) qt;\n"
      "endpackage\n"
      "localparam type UT = int;\n"
      "X #(UT::inner) ux;\n"
      "typedef X #(UT::inner) ut;\n"
      "interface ifo #(type T = int);\n"
      "  X #(T::inner) ix;\n"
      "  ifc #(.V(T::inner)) sub();\n"
      "endinterface\n"
      "module top #(type T = int);\n"
      "  localparam type LT = int;\n"
      "  typedef T::inner ti;\n"
      "  X #(T::inner) x1;\n"
      "  X #(.V(T::inner)) x2;\n"
      "  X #(ti) x3;\n"
      "  X #(X #(T::inner)) x4;\n"
      "  X #(LT::inner) x5;\n"
      "  X #($unit::UT::inner) x6;\n"
      "  X #(W#()::T::inner) x7;\n"
      "  Y #(T::P) y1;\n"
      "  Y #(.P(LT::P)) y2;\n"
      "  Y #(K::P) y3;\n"
      "  Y #($bits(T::inner)) y5;\n"
      "  typedef Y #(1 + T::P) yp;\n"
      "  typedef K KT;\n"
      "  X #(KT::inner) x8;\n"
      "  W #(T::inner)::T z1;\n"
      "  virtual ifc #(.V(T::inner)) vi;\n"
      "  m #(.V(), .P(T::P)) u6();\n"
      "  struct { X #(T::inner) h; } s1;\n"
      "  typedef X #(T::inner) xt;\n"
      "  localparam type XL = X #(T::inner);\n"
      "  var type(X #(T::inner)) xv;\n"
      "  m #(.V(T::inner)) u1();\n"
      "  m #(T::inner, T::P) u2();\n"
      "  m #(.V(ti), .P(T::P)) u3();\n"
      "  m #(.V(LT::inner)) u4();\n"
      "  m #(.V($unit::UT::inner)) u5();\n"
      "  ifc #(.V(T::inner)) i1();\n"
      "  prg #(.V(T::inner)) p1();\n"
      "  ifo io();\n"
      "  WY #(int) wy;\n"
      "  WB #(int) wb;\n"
      "  WF #(int) wf;\n"
      "  if (1) begin : g\n"
      "    X #(T::inner) gx;\n"
      "    m #(.V(T::inner)) gu();\n"
      "  end\n"
      "  initial begin X #(T::inner) bx; end\n"
      "  function automatic void mf(X #(T::inner) a); endfunction\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass,
                       {19, 20, 23, 24, 26, 27, 31, 32, 33, 35, 36, 37, 38,
                        39, 40, 42, 43, 46, 47, 48, 49, 50, 51, 52, 53, 54,
                        55, 56, 57, 58, 59, 61, 62, 63, 65, 66, 68, 69},
                       {34, 41, 45, 60});
}

TEST(TypeParameterElab,
     ClassSelectingOnlyInATypedefArgumentIsJudgedPerSpecialization) {
  ElabFixture f;
  Elaborate(
      "class K; typedef byte inner; endclass\n"
      "class X #(type V = int); endclass\n"
      "class W #(type T = K);\n"
      "  typedef X #(T::inner) wt;\n"
      "endclass\n"
      "class V #(type T);\n"
      "  typedef X #(T::inner) vt;\n"
      "endclass\n"
      "module top;\n"
      "  W #(int) wi;\n"
      "  W #(K) wk;\n"
      "  W #(5) w5;\n"
      "  V #() v0;\n"
      "endmodule\n",
      f);
  ExpectReportedOnlyOn(f, kNotAClass, {10}, {11});
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNotAClass, 12, "6.20.3"))
      << 12;
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNotAClass, 13, "6.20.3"))
      << 13;
}

}  // namespace
