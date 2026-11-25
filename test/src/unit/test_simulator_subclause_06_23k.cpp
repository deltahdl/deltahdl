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
    "class X #(type T = int); T v; endclass\n"
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
    for (bool hierarchical : {true, false}) {
      SCOPED_TRACE(place.open);
      SimFixture f;
      ElaborateSrc(std::string(kClasses)
                       .append("module n; logic [4:0] v; endmodule\n")
                       .append(place.open)
                       .append(hierarchical ? "\n X #(type(top.u.v)) a;\n"
                                            : "\n X #(type(s.v)) a;\n")
                       .append(place.close),
                   f);
      EXPECT_EQ(
          ReportedError(f.diag.Diagnostics(),
                        "type operator argument uses a hierarchical reference, "
                        "which the type operator does not accept",
                        kFirstLine + 2, "6.23"),
          hierarchical);
      EXPECT_EQ(f.has_errors, hierarchical);
    }
  }
}

TEST(SpecializationTypeRefArgumentElab, OperandThatNamesNothingIsReported) {
  for (const Place& place : kPlaces) {
    for (bool names : {false, true}) {
      SCOPED_TRACE(place.open);
      SimFixture f;
      ElaborateSrc(std::string(kClasses)
                       .append(place.open)
                       .append(names ? "  X #(type(pk::w9)) a;\n"
                                     : "  X #(type(nosuch)) a;\n")
                       .append(place.close),
                   f);
      const auto kLine = kFirstLine + std::ranges::count(place.open, '\n');
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of 'X' does not name a type",
                              static_cast<uint32_t>(kLine), "6.20.3"),
                !names);
      EXPECT_EQ(f.has_errors, !names);
    }
  }
}

}  // namespace
