#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kClasses =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  typedef struct packed { logic [3:0] a; bit b; } st;\n"
    "  typedef enum logic [2:0] { E, F } e_t;\n"
    "  parameter type PT = logic [4:0];\n"
    "  localparam type LT = t;\n"
    "  logic [8:0] w9;\n"
    "  parameter logic [4:0] P5 = 3;\n"
    "  class K; int m = 5; endclass\n"
    "  class X #(type T = int); T v; endclass\n"
    "endpackage\n"
    "class X #(type T = int); T v;"
    " function int w(); return $bits(v); endfunction endclass\n"
    "class Z #(int W = 1, type T = int); T v; logic [W-1:0] w; endclass\n";

constexpr int kFirstLine = 14;

std::string Printed(std::string_view source) {
  SimFixture f;
  return RunCapture(std::string(kClasses).append(source), f);
}

struct Place {
  std::string_view open;
  std::string_view close;
};

constexpr Place kPlaces[] = {
    {"module top;\n", "endmodule\n"},
    {"module top; d u(); endmodule\ninterface d;\n", "endinterface\n"},
    {"module top; d u(); endmodule\nprogram d;\n", "endprogram\n"},
    {"module top;\n  logic [1:0] n;\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"module top;\n  logic [1:0] n;\n"
     "  for (genvar i = 0; i < 1; i++) begin : g\n",
     "  end\nendmodule\n"},
};

constexpr Place kModuleAndGeneratePlaces[] = {kPlaces[0], kPlaces[1],
                                              kPlaces[3], kPlaces[4]};

void ExpectInEachPlace(std::string_view items, std::string_view printed) {
  for (const Place& place : kPlaces) {
    const std::string kSource =
        std::string(place.open).append(items).append(place.close);
    SCOPED_TRACE(kSource);
    EXPECT_EQ(Printed(kSource), printed);
  }
}

TEST(SpecializationTypeRefArgumentSim, NamesAVariable) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  X #(type(n)) a = new;\n"
      "  X #(.T(type(n))) b = new;\n"
      "  X #(logic [6:0]) c;\n"
      "  initial begin\n"
      "    c = a;\n"
      "    a.v = 300;\n"
      "    $display(\"%0d %0d %0d\", $bits(a.v), $bits(b.v), c.v);\n"
      "  end\n",
      "7 7 44\n");
}

TEST(SpecializationTypeRefArgumentSim, NamesAnExpressionAParameterOrAPackage) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  localparam logic [2:0] L = 1;\n"
      "  X #(type(n + 10'd0)) a = new;\n"
      "  X #(type(L)) b = new;\n"
      "  X #(type(pk::w9)) c = new;\n"
      "  X #(type(pk::P5)) d = new;\n"
      "  X #(.T(type({n, n}))) e = new;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(a.v), $bits(b.v),\n"
      "                   $bits(c.v), $bits(d.v), $bits(e.v));\n",
      "10 3 9 5 14\n");
}

TEST(SpecializationTypeRefArgumentSim, NamesADataTypeOrAClassHandle) {
  ExpectInEachPlace(
      "  pk::K k = new;\n"
      "  X #(type(pk::t)) a = new;\n"
      "  X #(type(logic [5:0])) b = new;\n"
      "  X #(type(k)) c = new;\n"
      "  X #(type(pk::K)) d = new;\n"
      "  initial begin\n"
      "    c.v = k;\n"
      "    d.v = k;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(a.v), $bits(b.v), c.v.m,\n"
      "             d.v.m);\n"
      "  end\n",
      "12 6 5 5\n");
}

TEST(SpecializationTypeRefArgumentSim, StandsBesideAValueArgument) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  Z #(3, type(n)) a = new;\n"
      "  Z #(.T(type(n)), .W(3)) b = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(a.v), $bits(a.w),\n"
      "                   $bits(b.v), $bits(b.w));\n",
      "7 3 7 3\n");
}

TEST(SpecializationTypeRefArgumentSim, EachInstanceAndIterationTakesItsOwn) {
  EXPECT_EQ(Printed("module m #(int W = 4) ();\n"
                    "  logic [W-1:0] n;\n"
                    "  X #(type(n)) a = new;\n"
                    "  initial #W $display(\"%0d %0d\", W, $bits(a.v));\n"
                    "endmodule\n"
                    "module top;\n"
                    "  m u();\n"
                    "  m #(6) w();\n"
                    "  for (genvar i = 8; i < 10; i++) begin : g\n"
                    "    logic [i-1:0] n;\n"
                    "    X #(type(n)) a = new;\n"
                    "    initial #i $display(\"%0d %0d\", i, $bits(a.v));\n"
                    "  end\n"
                    "endmodule\n"),
            "4 4\n6 6\n8 8\n9 9\n");
}

TEST(SpecializationTypeRefArgumentSim, TypesAnArrayOfHandles) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  X #(type(n)) a [2];\n"
      "  initial begin\n"
      "    a[1] = new;\n"
      "    a[1].v = 300;\n"
      "    $display(\"%0d %0d\", $bits(a[1].v), a[1].v);\n"
      "  end\n",
      "7 44\n");
}

TEST(SpecializationTypeRefArgumentSim, TypesAQueueOfHandles) {
  for (const Place& place : std::span(kPlaces).first(3)) {
    SCOPED_TRACE(place.open);
    EXPECT_EQ(Printed(std::string(place.open)
                          .append("  logic [6:0] n;\n"
                                  "  X #(type(n)) a = new;\n"
                                  "  X #(type(n)) q [$];\n"
                                  "  initial begin\n"
                                  "    q.push_back(a);\n"
                                  "    a.v = 300;\n"
                                  "    $display(\"%0d\", q[0].v);\n"
                                  "  end\n")
                          .append(place.close)),
              "44\n");
  }
}

TEST(SpecializationTypeRefArgumentSim, TypesAPackagesClassAndANestedArgument) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  pk::X #(type(n)) a = new;\n"
      "  X #(X #(type(n))) b = new;\n"
      "  X #(logic [6:0]) c = new;\n"
      "  initial begin\n"
      "    b.v = c;\n"
      "    b.v.v = 300;\n"
      "    $display(\"%0d %0d\", $bits(a.v), b.v.v);\n"
      "  end\n",
      "7 44\n");
}

TEST(SpecializationTypeRefArgumentSim, TakesAnArrayOperandsDimensions) {
  ExpectInEachPlace(
      "  typedef byte arr_t [4];\n"
      "  byte n [3];\n"
      "  int m [2][3];\n"
      "  arr_t u;\n"
      "  X #(type(n)) a = new;\n"
      "  X #(type(m)) b = new;\n"
      "  X #(type(u)) c = new;\n"
      "  X #(type(arr_t)) d = new;\n"
      "  initial begin\n"
      "    a.v[2] = 300;\n"
      "    b.v[1][2] = 5;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", $bits(a.v), a.v[2],\n"
      "             $bits(b.v), b.v[1][2], $bits(c.v), $bits(d.v));\n"
      "  end\n",
      "24 44 192 5 32 32\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, TakesAnArrayOperandsDimensions) {
  ExpectInEachPlace(
      "  byte n [3];\n"
      "  typedef X #(type(n)) xt;\n"
      "  xt a = new;\n"
      "  initial begin\n"
      "    a.v[2] = 300;\n"
      "    $display(\"%0d %0d\", $bits(a.v), a.v[2]);\n"
      "  end\n",
      "24 44\n");
}

TEST(SpecializationTypeRefArgumentSim, TakesAVariableSizedOperandsDimension) {
  ExpectInEachPlace(
      "  int q [$];\n"
      "  int y [];\n"
      "  int s [string];\n"
      "  X #(type(q)) a = new;\n"
      "  X #(type(y)) b = new;\n"
      "  X #(type(s)) c = new;\n"
      "  initial begin\n"
      "    a.v.push_back(7);\n"
      "    a.v.push_back(8);\n"
      "    b.v = new[3];\n"
      "    b.v[2] = 9;\n"
      "    c.v[\"k\"] = 4;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", a.v.size(), a.v[1],\n"
      "             b.v.size(), b.v[2], c.v.num(), c.v[\"k\"]);\n"
      "  end\n",
      "2 8 3 9 1 4\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim,
     TakesAVariableSizedOperandsDimension) {
  EXPECT_EQ(Printed("module top;\n"
                    "  int q [$];\n"
                    "  int y [];\n"
                    "  int s [string];\n"
                    "  typedef X #(type(q)) qt;\n"
                    "  typedef X #(type(y)) yt;\n"
                    "  typedef X #(type(s)) st;\n"
                    "  qt a = new;\n"
                    "  yt b = new;\n"
                    "  st c = new;\n"
                    "  initial begin\n"
                    "    a.v.push_back(7);\n"
                    "    a.v.push_back(8);\n"
                    "    b.v = new[3];\n"
                    "    b.v[2] = 9;\n"
                    "    c.v[\"k\"] = 4;\n"
                    "    $display(\"%0d %0d %0d %0d %0d %0d\", a.v.size(), "
                    "a.v[1],\n"
                    "             b.v.size(), b.v[2], c.v.num(), c.v[\"k\"]);\n"
                    "  end\n"
                    "endmodule\n"),
            "2 8 3 9 1 4\n");
}

constexpr std::string_view kArrayOperandLocals =
    "    X #(type(n)) a;\n"
    "    X #(type(m)) b;\n"
    "    a = new;\n"
    "    b = new;\n"
    "    a.v[2] = 300;\n"
    "    b.v[1][2] = 5;\n"
    "    $display(\"%0d %0d %0d %0d\", $bits(a.v), a.v[2], $bits(b.v),\n"
    "             b.v[1][2]);\n";

TEST(SpecializationTypeRefArgumentSim, TakesAnArrayOperandsDimensionsInALocal) {
  EXPECT_EQ(Printed(std::string("module top;\n"
                                "  byte n [3];\n"
                                "  int m [2][3];\n"
                                "  task automatic tk();\n")
                        .append(kArrayOperandLocals)
                        .append("  endtask\n"
                                "  function automatic void fn();\n")
                        .append(kArrayOperandLocals)
                        .append("  endfunction\n"
                                "  initial begin\n")
                        .append(kArrayOperandLocals)
                        .append("    tk();\n"
                                "    fn();\n"
                                "  end\n"
                                "endmodule\n")),
            "24 44 192 5\n24 44 192 5\n24 44 192 5\n");
}

TEST(SpecializationTypeRefArgumentSim,
     TakesAnArrayOperandsDimensionsInAClassPropertyOrExtends) {
  EXPECT_EQ(Printed("module top;\n"
                    "  byte n [3];\n"
                    "  int m [2][3];\n"
                    "  class H;\n"
                    "    X #(type(n)) p = new;\n"
                    "    X #(type(m)) q = new;\n"
                    "  endclass\n"
                    "  class D extends X #(type(n)); endclass\n"
                    "  class E extends X #(type(m)); endclass\n"
                    "  H h = new;\n"
                    "  D d = new;\n"
                    "  E e = new;\n"
                    "  initial\n"
                    "    $display(\"%0d %0d %0d %0d\", $bits(h.p.v), "
                    "$bits(h.q.v),\n"
                    "             $bits(d.v), $bits(e.v));\n"
                    "endmodule\n"),
            "24 192 24 192\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, NamesAVariableOrderedOrNamed) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  typedef X #(type(n)) at;\n"
      "  typedef X #(.T(type(n))) bt;\n"
      "  at a = new, d [2];\n"
      "  bt b = new;\n"
      "  X #(logic [6:0]) c;\n"
      "  initial begin\n"
      "    c = a;\n"
      "    a.v = 300;\n"
      "    d[1] = a;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(a.v), $bits(b.v), c.v,\n"
      "             d[1].v);\n"
      "  end\n",
      "7 7 44 44\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, NamesEachOtherOperand) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  localparam logic [2:0] L = 1;\n"
      "  pk::K k = new;\n"
      "  typedef X #(type(n + 10'd0)) at;\n"
      "  typedef X #(.T(type(L))) bt;\n"
      "  typedef X #(type(pk::w9)) ct;\n"
      "  typedef X #(.T(type(pk::t))) dt;\n"
      "  typedef X #(type(k)) et;\n"
      "  typedef X #(type(logic [5:0])) ft;\n"
      "  at a = new;\n"
      "  bt b = new;\n"
      "  ct c = new;\n"
      "  dt d = new;\n"
      "  et e = new;\n"
      "  ft g = new;\n"
      "  initial begin\n"
      "    e.v = k;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", $bits(a.v), $bits(b.v),\n"
      "             $bits(c.v), $bits(d.v), e.v.m, $bits(g.v));\n"
      "  end\n",
      "10 3 9 12 5 6\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, EachInstanceTakesItsOwn) {
  EXPECT_EQ(Printed("module m #(int W = 4) ();\n"
                    "  logic [W-1:0] n;\n"
                    "  typedef X #(type(n)) xt;\n"
                    "  typedef xt yt;\n"
                    "  xt a = new;\n"
                    "  yt b = new;\n"
                    "  initial #W $display(\"%0d %0d %0d\", W, $bits(a.v),\n"
                    "                      $bits(b.v));\n"
                    "endmodule\n"
                    "module top;\n"
                    "  m u();\n"
                    "  m #(6) w();\n"
                    "  for (genvar i = 8; i < 10; i++) begin : g\n"
                    "    logic [i-1:0] n;\n"
                    "    typedef X #(type(n)) xt;\n"
                    "    xt a = new;\n"
                    "    initial #i $display(\"%0d %0d\", i, $bits(a.v));\n"
                    "  end\n"
                    "endmodule\n"),
            "4 4 4\n6 6 6\n8 8\n9 9\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, NamesATypedefOrASpecialization) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  typedef X #(type(n)) xt;\n"
      "  typedef xt yt;\n"
      "  typedef X #(X #(type(n))) zt;\n"
      "  yt a = new;\n"
      "  zt b = new;\n"
      "  X #(logic [6:0]) c = new;\n"
      "  initial begin\n"
      "    b.v = c;\n"
      "    b.v.v = 300;\n"
      "    $display(\"%0d %0d\", $bits(a.v), b.v.v);\n"
      "  end\n",
      "7 44\n");
}

TEST(SpecializationTypedefTypeRefArgumentSim, TypesALocalAFormalAndAProperty) {
  for (const Place& place : std::span(kPlaces).first(3)) {
    SCOPED_TRACE(place.open);
    EXPECT_EQ(
        Printed(std::string(place.open)
                    .append("  logic [6:0] n;\n"
                            "  typedef X #(type(n)) xt;\n"
                            "  class D; xt p = new; endclass\n"
                            "  D d = new;\n"
                            "  function int f(xt a); return a.v; endfunction\n"
                            "  initial begin\n"
                            "    automatic xt b = new;\n"
                            "    b.v = 300;\n"
                            "    $display(\"%0d %0d %0d %0d\", $bits(b.v),\n"
                            "             b.v, f(b), $bits(d.p.v));\n"
                            "  end\n")
                    .append(place.close)),
        "7 44 44 7\n");
  }
}

TEST(ProceduralSpecializationTypeRefArgumentSim, NamesTheScopesOrABlocksOwn) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  initial begin\n"
      "    logic [3:0] l;\n"
      "    X #(type(n)) a;\n"
      "    X #(type(l)) b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    a.v = 300;\n"
      "    b.v = 300;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(a.v), a.v, $bits(b.v), b.v);\n"
      "  end\n",
      "7 44 4 12\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, StandsInEachProcedure) {
  for (const Place& place : kModuleAndGeneratePlaces) {
    SCOPED_TRACE(place.open);
    SimFixture f;
    EXPECT_EQ(RunCaptureThroughFinals(
                  ElaborateSrc,
                  std::string(kClasses)
                      .append(place.open)
                      .append("  logic [6:0] n;\n"
                              "  bit go;\n"
                              "  always @(go) begin\n"
                              "    automatic X #(type(n)) a = new;\n"
                              "    $display(\"%0d\", $bits(a.v));\n"
                              "  end\n"
                              "  initial begin\n"
                              "    fork\n"
                              "      begin\n"
                              "        automatic X #(type(n)) a = new;\n"
                              "        $display(\"%0d\", $bits(a.v));\n"
                              "      end\n"
                              "    join\n"
                              "    go = 1;\n"
                              "  end\n"
                              "  final begin\n"
                              "    automatic X #(type(n)) a = new;\n"
                              "    $display(\"%0d\", $bits(a.v));\n"
                              "  end\n")
                      .append(place.close),
                  f),
              "7\n7\n7\n");
  }
}

TEST(ProceduralSpecializationTypeRefArgumentSim, StandsInATaskOrFunction) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  task tk(logic [4:0] p);\n"
      "    automatic X #(type(n)) a = new;\n"
      "    automatic X #(type(p)) b = new;\n"
      "    $display(\"%0d %0d\", $bits(a.v), $bits(b.v));\n"
      "  endtask\n"
      "  function int f(logic [4:0] p);\n"
      "    logic [2:0] l;\n"
      "    X #(type(n)) a;\n"
      "    X #(type(p)) b;\n"
      "    X #(type(l)) c;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    c = new;\n"
      "    return $bits(a.v) * 100 + $bits(b.v) * 10 + $bits(c.v);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    tk(0);\n"
      "    $display(\"%0d\", f(0));\n"
      "  end\n",
      "7 5\n753\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, TypesAFormalAndAReturn) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  X #(logic [6:0]) x = new;\n"
      "  function int f(X #(type(n)) a); return $bits(a.v); endfunction\n"
      "  function X #(type(n)) g(X #(logic [6:0]) a); g = a; endfunction\n"
      "  function X #(type(n)) h();\n"
      "    X #(type(n)) a;\n"
      "    a = new;\n"
      "    return a;\n"
      "  endfunction\n"
      "  task tk(input X #(type(n)) a, output X #(type(n)) b);\n"
      "    b = a;\n"
      "  endtask\n"
      "  initial begin\n"
      "    X #(logic [6:0]) y;\n"
      "    tk(x, y);\n"
      "    y.v = 300;\n"
      "    $display(\"%0d %0d\", f(x), y.v);\n"
      "    y = g(x);\n"
      "    y.v = 300;\n"
      "    $display(\"%0d\", y.v);\n"
      "    y = h();\n"
      "    $display(\"%0d\", y.w());\n"
      "  end\n",
      "7 44\n44\n7\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, TypesALocalTypedef) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  task tk;\n"
      "    logic [4:0] l;\n"
      "    typedef X #(type(l)) yt;\n"
      "    yt b;\n"
      "    b = new;\n"
      "    $display(\"%0d\", $bits(b.v));\n"
      "  endtask\n"
      "  initial begin\n"
      "    typedef X #(type(n)) xt;\n"
      "    xt a;\n"
      "    a = new;\n"
      "    $display(\"%0d\", $bits(a.v));\n"
      "    tk;\n"
      "  end\n",
      "7\n5\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, NamesTheLocalThatHides) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  initial begin\n"
      "    X #(type(n)) a;\n"
      "    begin\n"
      "      logic [2:0] n;\n"
      "      X #(type(n)) b;\n"
      "      b = new;\n"
      "      $display(\"%0d\", $bits(b.v));\n"
      "    end\n"
      "    a = new;\n"
      "    $display(\"%0d\", $bits(a.v));\n"
      "  end\n",
      "3\n7\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, NamesEachOtherOperand) {
  ExpectInEachPlace(
      "  logic [6:0] n;\n"
      "  localparam logic [2:0] L = 1;\n"
      "  initial begin\n"
      "    automatic pk::K k = new;\n"
      "    X #(type(n + 10'd0)) a;\n"
      "    X #(.T(type(L))) b;\n"
      "    X #(type(pk::w9)) c;\n"
      "    X #(.T(type(pk::t))) d;\n"
      "    X #(type(k)) e;\n"
      "    X #(type(logic [5:0])) g;\n"
      "    Z #(3, type(n)) h;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    c = new;\n"
      "    d = new;\n"
      "    e = new;\n"
      "    g = new;\n"
      "    h = new;\n"
      "    e.v = k;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(a.v), $bits(b.v), $bits(c.v),\n"
      "             $bits(d.v));\n"
      "    $display(\"%0d %0d %0d %0d\", e.v.m, $bits(g.v), $bits(h.v),\n"
      "             $bits(h.w));\n"
      "  end\n",
      "10 3 9 12\n5 6 7 3\n");
}

TEST(ProceduralSpecializationTypeRefArgumentSim, StandsInAPackageOrTheUnit) {
  EXPECT_EQ(Printed("package p2;\n"
                    "  logic [6:0] n;\n"
                    "  function int f(X #(type(n)) a);\n"
                    "    logic [3:0] l;\n"
                    "    X #(type(n)) b;\n"
                    "    X #(type(l)) c;\n"
                    "    b = a;\n"
                    "    c = new;\n"
                    "    return $bits(b.v) * 10 + $bits(c.v);\n"
                    "  endfunction\n"
                    "endpackage\n"
                    "logic [4:0] m;\n"
                    "function X #(type(m)) g();\n"
                    "  X #(type(m)) a;\n"
                    "  a = new;\n"
                    "  return a;\n"
                    "endfunction\n"
                    "task tk(logic [2:0] q);\n"
                    "  automatic X #(type(m)) a = new;\n"
                    "  automatic X #(type(q)) b = new;\n"
                    "  $display(\"%0d %0d\", $bits(a.v), $bits(b.v));\n"
                    "endtask\n"
                    "module top;\n"
                    "  initial begin\n"
                    "    X #(logic [4:0]) y;\n"
                    "    automatic X #(logic [6:0]) x = new;\n"
                    "    $display(\"%0d\", p2::f(x));\n"
                    "    tk(0);\n"
                    "    y = g();\n"
                    "    $display(\"%0d\", y.w());\n"
                    "  end\n"
                    "endmodule\n"),
            "74\n5 3\n5\n");
}

TEST(PackageTypeTypeRefSim, DeclaresAVariableALocalAFormalAndAProperty) {
  ExpectInEachPlace(
      "  var type(pk::t) a;\n"
      "  function int f(var type(pk::t) b); return b; endfunction\n"
      "  class P; var type(pk::t) c; endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    var type(pk::t) d;\n"
      "    p.c = 5000;\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(a), f(5000), p.c, $bits(d));\n"
      "  end\n",
      "12 904 904 12\n");
}

TEST(PackageTypeTypeRefSim, NamesAStructureATypeParameterAndAClass) {
  ExpectInEachPlace(
      "  var type(pk::st) s;\n"
      "  var type(pk::PT) p;\n"
      "  var type(pk::LT) l;\n"
      "  var type(pk::K) k = new;\n"
      "  initial begin\n"
      "    s.a = 9;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", s.a, $bits(s), $bits(p),\n"
      "             $bits(l), k.m);\n"
      "  end\n",
      "9 5 5 12 5\n");
}

TEST(PackageTypeTypeRefSim, NamesAStructureOfALocalAFormalAndAProperty) {
  ExpectInEachPlace(
      "  function int f(var type(pk::st) b); return b.a; endfunction\n"
      "  class P; var type(pk::st) c; endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    var type(pk::st) d;\n"
      "    d.a = 25;\n"
      "    p.c = 52;\n"
      "    $display(\"%0d %0d %0d %0d\", d.a, $bits(d), f(d), p.c);\n"
      "  end\n",
      "9 5 9 20\n");
}

TEST(PackageTypeTypeRefSim, NamesATypeParameterOfALocalAFormalAndAProperty) {
  ExpectInEachPlace(
      "  function int f(var type(pk::PT) b); return b; endfunction\n"
      "  function int g(var type(pk::LT) b); return b; endfunction\n"
      "  class P; var type(pk::PT) c; var type(pk::LT) d; endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    var type(pk::PT) x;\n"
      "    var type(pk::LT) y;\n"
      "    p.c = 5000;\n"
      "    p.d = 5000;\n"
      "    $display(\"%0d %0d %0d\", $bits(x), f(5000), p.c);\n"
      "    $display(\"%0d %0d %0d\", $bits(y), g(5000), p.d);\n"
      "  end\n",
      "5 8 8\n12 904 904\n");
}

TEST(PackageTypeTypeRefSim, NamesAClassOfALocalAFormalAndAProperty) {
  ExpectInEachPlace(
      "  function int f(var type(pk::K) b); return b.m; endfunction\n"
      "  class P; var type(pk::K) c = new; endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    var automatic type(pk::K) d = new;\n"
      "    d.m = 6;\n"
      "    p.c.m = 7;\n"
      "    $display(\"%0d %0d %0d\", d.m, f(d), p.c.m);\n"
      "  end\n",
      "6 6 7\n");
}

TEST(PackageTypeTypeRefSim, NamesAnEnumeration) {
  for (const Place& place : std::span(kPlaces).first(3)) {
    SCOPED_TRACE(place.open);
    EXPECT_EQ(Printed(std::string(place.open)
                          .append("  var type(pk::e_t) e;\n"
                                  "  initial begin\n"
                                  "    e = pk::F;\n"
                                  "    $display(\"%0d %s\", $bits(e),\n"
                                  "             e.name());\n"
                                  "  end\n")
                          .append(place.close)),
              "3 F\n");
  }
}

constexpr Place kModulePlaces[] = {
    {"module top; n u(); struct packed { bit v; } s;", " endmodule\n"},
    {"module top; n u(); struct packed { bit v; } s; if (1) begin : g",
     " end endmodule\n"},
    {"module top; n u(); d x(); endmodule interface d; struct packed { bit v; "
     "} s;",
     " endinterface\n"},
    {"module top; n u(); d x(); endmodule program d; struct packed { bit v; } "
     "s;",
     " endprogram\n"},
    {"module top; n u(); struct packed { bit v; } s; for (genvar i = 0; i < 2; "
     "i++) begin : g",
     " end endmodule\n"},
};

TEST(SpecializationTypeRefArgumentElab, HierarchicalOperandIsReported) {
  for (const Place& place : kModulePlaces) {
    for (std::string_view declaration :
         {"X #(type(top.u.v)) a;", "X #(type(s.v)) a;",
          "typedef X #(type(top.u.v)) a;", "typedef X #(type(s.v)) a;",
          "initial begin X #(type(top.u.v)) a; end",
          "initial begin X #(type(s.v)) a; end"}) {
      SCOPED_TRACE(std::string(place.open).append(declaration));
      const bool kHierarchical = declaration.contains("top.u.v");
      SimFixture f;
      ElaborateSrc(std::string(kClasses)
                       .append("module n; logic [4:0] v; endmodule\n")
                       .append(place.open)
                       .append("\n")
                       .append(declaration)
                       .append("\n")
                       .append(place.close),
                   f);
      EXPECT_EQ(
          ReportedError(f.diag.Diagnostics(),
                        "type operator argument uses a hierarchical reference, "
                        "which the type operator does not accept",
                        kFirstLine + 2, "6.23"),
          kHierarchical);
      EXPECT_EQ(f.has_errors, kHierarchical);
    }
  }
}

TEST(SpecializationTypeRefArgumentElab, OperandThatNamesNothingIsReported) {
  for (const Place& place : kPlaces) {
    for (std::string_view declaration :
         {"X #(type(pk::w9)) a;", "X #(type(nosuch)) a;",
          "typedef X #(type(pk::w9)) a;", "typedef X #(type(nosuch)) a;",
          "initial begin X #(type(pk::w9)) a; end",
          "initial begin X #(type(nosuch)) a; end"}) {
      SCOPED_TRACE(std::string(place.open).append(declaration));
      const bool kNames = declaration.contains("pk::w9");
      SimFixture f;
      ElaborateSrc(std::string(kClasses)
                       .append(place.open)
                       .append(declaration)
                       .append("\n")
                       .append(place.close),
                   f);
      const auto kLine = kFirstLine + std::ranges::count(place.open, '\n');
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of 'X' does not name a type",
                              static_cast<uint32_t>(kLine), "6.20.3"),
                !kNames);
      EXPECT_EQ(f.has_errors, !kNames);
    }
  }
}

}  // namespace
