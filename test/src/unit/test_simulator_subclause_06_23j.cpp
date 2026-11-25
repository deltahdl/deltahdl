#include <gtest/gtest.h>

#include <cstddef>
#include <span>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kPackage =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  struct packed { bit f; bit g; } s;\n"
    "  class K;\n"
    "    int v = 7;\n"
    "    typedef logic [3:0] t2;\n"
    "    static logic [4:0] sv;\n"
    "    class N; typedef logic [2:0] t3; endclass\n"
    "  endclass\n"
    "endpackage\n";

std::string Printed(std::string_view source) {
  SimFixture f;
  return RunCapture(std::string(kPackage).append(source), f);
}

struct ClassPlace {
  std::string_view name;
  std::string_view before;
  std::string_view after;
};

std::string AsName(std::string text, std::string_view name) {
  for (size_t at = text.find('@'); at != std::string::npos; at = text.find('@'))
    text.replace(at, 1, name);
  return text;
}

constexpr ClassPlace kClassPlaces[] = {
    {"W", "", "module top;\n"},
    {"r::W", "package r;\n", "endpackage\nmodule top;\n"},
    {"W", "module top;\n", ""},
    {"W",
     "module top; d u(); endmodule\n"
     "interface d;\n",
     ""},
    {"W",
     "module top; d u(); endmodule\n"
     "program d;\n",
     ""},
    {"W", "module top;\n  if (1) begin : g\n", ""},
};

std::string_view Closing(const ClassPlace& place) {
  if (place.before.find("interface") != std::string_view::npos)
    return "endinterface\n";
  if (place.before.find("program") != std::string_view::npos)
    return "endprogram\n";
  if (place.before.find("begin") != std::string_view::npos)
    return "end\nendmodule\n";
  return "endmodule\n";
}

std::string InPlace(const ClassPlace& place, std::string_view declarations,
                    std::string_view uses) {
  return AsName(std::string(place.before)
                    .append(declarations)
                    .append(place.after)
                    .append(uses)
                    .append(Closing(place)),
                place.name);
}

void ExpectFromAClassInEachPlace(std::string_view declarations,
                                 std::string_view uses,
                                 std::string_view printed) {
  for (const ClassPlace& place : kClassPlaces) {
    const std::string kSource = InPlace(place, declarations, uses);
    SCOPED_TRACE(kSource);
    EXPECT_EQ(Printed(kSource), printed);
  }
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultNamesADataType) {
  ExpectFromAClassInEachPlace(
      "class W #(type T = type(logic [6:0]), U = type(pk::t));\n"
      "  T a; U b;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  @ #(byte) x = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(x.a), $bits(x.b));\n",
      "7 12 8 12\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultNamesAValueAroundTheClass) {
  ExpectFromAClassInEachPlace(
      "logic [4:0] n;\n"
      "class W #(type T = type(n), U = type(n + 8'b0), V = type(pk::w9),\n"
      "          X = type({n, n}));\n"
      "  T a; U b; V c; X d;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  @ #(.U(byte)) x = new;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c), $bits(w.d), $bits(x.b));\n",
      "5 8 9 10 8\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultNamesAnEarlierValueParameter) {
  ExpectFromAClassInEachPlace(
      "class W #(shortint P = 3, type T = type(P), U = type(P + 40'b0));\n"
      "  T a; U b;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d\", $bits(w.a), $bits(w.b));\n",
      "16 40\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultNamesAParameterWithoutAWrittenType) {
  ExpectFromAClassInEachPlace(
      "logic [8:0] n;\n"
      "class W #(parameter P = 8'd3, type(n) Q = 1, byte R[2] = '{1, 2},\n"
      "          type T = type(P), U = type({P, P}), V = type(Q),\n"
      "          X = type(R[0]));\n"
      "  T a; U b; V c; X d;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c), $bits(w.d));\n",
      "8 16 9 8\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultStandsBesideAParameterWithNoValue) {
  ExpectFromAClassInEachPlace(
      "logic [8:0] n;\n"
      "class W #(P, type T = type(n));\n"
      "  T a;\n"
      "endclass\n",
      "  @ #(4) w = new;\n"
      "  initial $display(\"%0d\", $bits(w.a));\n",
      "9\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultOfANestedClass) {
  ExpectFromAClassInEachPlace(
      "logic [8:0] n;\n"
      "class W;\n"
      "  class N #(type T = byte, U = type(n)); T a; U b; endclass\n"
      "  N h = new;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d\", $bits(w.h.a), $bits(w.h.b));\n",
      "8 9\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesAPropertyOfAReferencedType) {
  ExpectFromAClassInEachPlace(
      "logic [8:0] n;\n"
      "class W #(int N = 1);\n"
      "  var type(n) q;\n"
      "  localparam type T = type(q);\n"
      "  T a;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d\", $bits(w.a));\n",
      "9\n");
}

TEST(ClassTypeRefDefaultSim, HeaderDefaultNamesAClassHandle) {
  ExpectFromAClassInEachPlace(
      "class J; int v = 7; endclass\n"
      "J k;\n"
      "class W #(type T = type(k), U = type(J));\n"
      "  T a = new; U b = new;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d\", w.a.v, w.b.v);\n",
      "7 7\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesADataType) {
  ExpectFromAClassInEachPlace(
      "class W;\n"
      "  localparam type T = type(logic [6:0]), V = type(byte);\n"
      "  parameter type U = type(pk::t);\n"
      "  T a; U b; V c;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c));\n",
      "7 12 8\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesAProperty) {
  ExpectFromAClassInEachPlace(
      "class W;\n"
      "  logic [4:0] q;\n"
      "  localparam type T = type(q), U = type(q + 8'b0);\n"
      "  localparam type V = type(this.q), X = type({q, q});\n"
      "  T a; U b; V c; X d;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c), $bits(w.d));\n",
      "5 8 5 10\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueTypesAMethodOfTheClass) {
  for (const ClassPlace& place : kClassPlaces) {
    if (place.name != "W") continue;
    const std::string kSource =
        InPlace(place,
                "class W;\n"
                "  logic [4:0] q;\n"
                "  localparam type T = type(q), U = type(q + 8'b0);\n"
                "  function int f(U u); T l;\n"
                "    l = 40; return l * 1000 + $bits(l) * 10 + $bits(u);\n"
                "  endfunction\n"
                "endclass\n",
                "  @ w = new;\n"
                "  initial $display(\"%0d\", w.f(1));\n");
    SCOPED_TRACE(kSource);
    EXPECT_EQ(Printed(kSource), "8058\n");
  }
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesAnInheritedProperty) {
  for (const ClassPlace& place : kClassPlaces) {
    if (place.before.find("begin") != std::string_view::npos) continue;
    const std::string kSource =
        InPlace(place,
                "class B; logic [4:0] q; endclass\n"
                "class W extends B;\n"
                "  localparam type T = type(q), U = type(q + 8'b0);\n"
                "  T a; U b;\n"
                "endclass\n",
                "  @ w = new;\n"
                "  initial $display(\"%0d %0d\", $bits(w.a), $bits(w.b));\n");
    SCOPED_TRACE(kSource);
    EXPECT_EQ(Printed(kSource), "5 8\n");
  }
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesAValueAroundTheClass) {
  ExpectFromAClassInEachPlace(
      "logic [4:0] n;\n"
      "logic [2:0] q;\n"
      "class W;\n"
      "  logic [5:0] q;\n"
      "  localparam type T = type(n), U = type(n + 8'b0), V = type(pk::w9),\n"
      "                  X = type(q);\n"
      "  T a; U b; V c; X d;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c), $bits(w.d));\n",
      "5 8 9 6\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueNamesAClassHandle) {
  ExpectFromAClassInEachPlace(
      "class W;\n"
      "  pk::K k;\n"
      "  localparam type T = type(k), U = type(pk::K);\n"
      "  T a = new; U b = new;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d\", w.a.v, w.b.v);\n",
      "7 7\n");
}

TEST(ClassTypeRefDefaultSim, TypedefOfAReferenceTakesTheReferencedType) {
  ExpectFromAClassInEachPlace(
      "logic [2:0] n;\n"
      "class W;\n"
      "  logic [4:0] q;\n"
      "  typedef type(q) T;\n"
      "  typedef type(q + 8'b0) U;\n"
      "  typedef type(n) V;\n"
      "  typedef type(pk::w9) X;\n"
      "  T a; U b; V c; X d;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $bits(w.a), $bits(w.b),\n"
      "                   $bits(w.c), $bits(w.d));\n",
      "5 8 3 9\n");
}

TEST(ClassTypeRefDefaultSim, BodyValueOfANestedClass) {
  ExpectFromAClassInEachPlace(
      "class W;\n"
      "  class I;\n"
      "    logic [4:0] q;\n"
      "    localparam type T = type(q), U = type(logic [6:0]);\n"
      "    T a; U b;\n"
      "  endclass\n"
      "  I i = new;\n"
      "endclass\n",
      "  @ w = new;\n"
      "  initial $display(\"%0d %0d\", $bits(w.i.a), $bits(w.i.b));\n",
      "5 7\n");
}

struct ParameterScope {
  std::string_view open;
  std::string_view close;
  std::string_view prefix;
};

constexpr ParameterScope kParameterScopes[] = {
    {"package r;\n", "endpackage\n", "r::"},
    {"package r;\n", "endpackage\nimport r::*;\n", ""},
    {"", "", ""},
    {"", "", "$unit::"},
};

void ExpectFromAParameterInEachScope(
    std::string_view declarations, std::string_view uses,
    std::string_view printed,
    std::span<const ParameterScope> scopes = kParameterScopes) {
  for (const ParameterScope& scope : scopes) {
    const std::string kSource = AsName(std::string(scope.open)
                                           .append(declarations)
                                           .append(scope.close)
                                           .append("module top;\n")
                                           .append(uses)
                                           .append("endmodule\n"),
                                       scope.prefix);
    SCOPED_TRACE(kSource);
    EXPECT_EQ(Printed(kSource), printed);
  }
}

TEST(ScopeTypeRefParamSim, ValueNamesADataType) {
  ExpectFromAParameterInEachScope(
      "parameter type T = type(logic [6:0]);\n"
      "localparam type U = type(pk::t), V = type(byte);\n"
      "T a; U b; V c;\n",
      "  @T x; @U y; @V z;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d %0d\", $bits(@a), $bits(@b),\n"
      "                   $bits(@c), $bits(x), $bits(y), $bits(z));\n",
      "7 12 8 7 12 8\n");
}

TEST(ScopeTypeRefParamSim, ValueNamesAValue) {
  ExpectFromAParameterInEachScope(
      "logic [4:0] n;\n"
      "parameter shortint P = 3;\n"
      "parameter type T = type(n), U = type(n + 8'b0);\n"
      "localparam type V = type(pk::w9), X = type(P), Y = type({n, n});\n"
      "T a; U b; V c; X d; Y e;\n",
      "  @T x; @U y; @V z; @X s; @Y t;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d %0d %0d\", $bits(@a), $bits(@b),\n"
      "             $bits(@c), $bits(@d), $bits(@e));\n"
      "    $display(\"%0d %0d %0d %0d %0d\", $bits(x), $bits(y), $bits(z),\n"
      "             $bits(s), $bits(t));\n"
      "  end\n",
      "5 8 9 16 10\n5 8 9 16 10\n");
}

TEST(ScopeTypeRefParamSim, ValueNamesAnotherParametersType) {
  ExpectFromAParameterInEachScope(
      "logic [4:0] n;\n"
      "parameter type T = type(n + 8'b0);\n"
      "parameter int W = 8;\n"
      "T a;\n"
      "parameter type U = type(T), V = type({a, a});\n"
      "parameter type X = type(logic [W-2:0]), Y = type({W{1'b0}});\n"
      "U b; V c; Y e;\n",
      "  @X x;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(@a), $bits(@b),\n"
      "                   $bits(@c), $bits(x), $bits(@e));\n",
      "8 8 16 7 8\n");
}

TEST(ScopeTypeRefParamSim, ValueNamesAnArray) {
  for (size_t scope : {0, 2, 3}) {
    ExpectFromAParameterInEachScope(
        "logic [4:0] n [3];\n"
        "typedef type(n) td;\n"
        "parameter type T = type(n);\n",
        "  initial begin\n"
        "    @T x; @td b;\n"
        "    $display(\"%0d %0d\", $bits(x), $bits(b));\n"
        "  end\n",
        "15 15\n", std::span(kParameterScopes).subspan(scope, 1));
  }
}

TEST(ScopeTypeRefParamSim, ValueNamesAStructureAMemberAndAnEnumeration) {
  ExpectFromAParameterInEachScope(
      "struct packed { logic [2:0] f; bit g; } s;\n"
      "enum logic [1:0] { A, B, C } e;\n"
      "parameter type U = type(s), V = type(s.f);\n"
      "parameter type X = type(e);\n",
      "  @U y; @V z; @X u;\n"
      "  initial begin\n"
      "    y.f = 5;\n"
      "    u = u.last();\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(y), y.f, $bits(z), u);\n"
      "  end\n",
      "4 5 3 2\n");
}

TEST(ScopeTypeRefParamSim, ValueNamesAClassHandleAndACall) {
  ExpectFromAParameterInEachScope(
      "class J; int v = 7; endclass\n"
      "J k;\n"
      "function logic [9:0] f(); return 0; endfunction\n"
      "parameter type T = type(k), U = type(J), V = type(f());\n",
      "  @T a = new; @U b = new; @V c;\n"
      "  initial $display(\"%0d %0d %0d\", a.v, b.v, $bits(c));\n",
      "7 7 10\n");
}

TEST(ScopeTypeRefParamSim, ParameterTypesASubroutineAndAClassOfItsScope) {
  ExpectFromAParameterInEachScope(
      "logic [4:0] n;\n"
      "parameter type T = type(n), U = type(n + 8'b0);\n"
      "function int f(U u); T l; return $bits(l) * 100 + $bits(u);\n"
      "endfunction\n"
      "class Q; T p; U q; endclass\n",
      "  @Q h = new;\n"
      "  initial $display(\"%0d %0d %0d\", @f(1), $bits(h.p), $bits(h.q));\n",
      "508 5 8\n", std::span(kParameterScopes).subspan(1));
}

TEST(ScopeTypeRefParamSim, TypedefOfAnExpressionsTypeIsNoForwardDeclaration) {
  ExpectFromAParameterInEachScope(
      "logic [4:0] n;\n"
      "typedef type(n + 8'b0) T;\n"
      "typedef type(pk::w9) V;\n"
      "T a; V c;\n",
      "  @T x;\n"
      "  initial $display(\"%0d %0d %0d\", $bits(@a), $bits(@c), $bits(x));\n",
      "8 9 8\n");
}

struct Procedure {
  std::string_view open;
  std::string_view close;
};

constexpr Procedure kProcedures[] = {
    {"module top;\n  initial begin\n", "  end\nendmodule\n"},
    {"module top;\n  initial begin begin\n", "  end end\nendmodule\n"},
    {"module top;\n  task f();\n", "  endtask\n  initial f();\nendmodule\n"},
    {"module top;\n  function void f();\n",
     "  endfunction\n  initial f();\nendmodule\n"},
    {"class C;\n  function void f();\n",
     "  endfunction\nendclass\nmodule top;\n  C c = new;\n"
     "  initial c.f();\nendmodule\n"},
    {"module top;\n  class C;\n  task f();\n",
     "  endtask\n  endclass\n  C c = new;\n  initial c.f();\nendmodule\n"},
    {"interface d;\n  initial begin\n",
     "  end\nendinterface\nmodule top; d u(); endmodule\n"},
    {"program d;\n  initial begin\n",
     "  end\nendprogram\nmodule top; d u(); endmodule\n"},
};

TEST(BlockTypeRefParamSim, ValueNamesALocalAPackageAndADataType) {
  for (const Procedure& procedure : kProcedures) {
    SCOPED_TRACE(procedure.open);
    EXPECT_EQ(
        Printed(std::string(procedure.open)
                    .append("logic [4:0] n;\n"
                            "logic [2:0] m;\n"
                            "localparam type T = type(n);\n"
                            "parameter type U = type(n + 8'b0);\n"
                            "localparam type V = type(pk::w9), X = type(pk::t),"
                            " Y = type(logic [6:0]);\n"
                            "T a; U b; V c; X d; Y e;\n"
                            "$display(\"%0d %0d %0d %0d %0d\", $bits(a),\n"
                            "         $bits(b), $bits(c), $bits(d),\n"
                            "         $bits(e));\n")
                    .append(procedure.close)),
        "5 8 9 12 7\n");
  }
}

TEST(BlockTypeRefParamSim, TypedefOfAReferenceTakesTheReferencedType) {
  for (const Procedure& procedure : kProcedures) {
    SCOPED_TRACE(procedure.open);
    EXPECT_EQ(Printed(std::string(procedure.open)
                          .append("import pk::*;\n"
                                  "logic [4:0] n;\n"
                                  "typedef type(n) T;\n"
                                  "typedef type(n + 8'b0) U;\n"
                                  "typedef type(pk::w9) V;\n"
                                  "T a; U b; V c;\n"
                                  "$display(\"%0d %0d %0d\", $bits(a),\n"
                                  "         $bits(b), $bits(c));\n")
                          .append(procedure.close)),
              "5 8 9\n");
  }
}

constexpr std::string_view kHierarchical =
    "type operator argument uses a hierarchical reference, which the type "
    "operator does not accept";

struct Written {
  std::string_view open;
  std::string_view close;
};

constexpr Written kWrittenPlaces[] = {
    {"class W #(type T = ", "); endclass\nmodule top; W w; endmodule\n"},
    {"class W; localparam type T = ", "; endclass\nmodule top; endmodule\n"},
    {"package r; parameter type T = ", "; endpackage\nmodule top; endmodule\n"},
    {"localparam type T = ", ";\nmodule top; endmodule\n"},
    {"module top; class W #(type T = ", "); endclass W w; endmodule\n"},
    {"module top; class W; localparam type T = ", "; endclass endmodule\n"},
    {"module top; initial begin localparam type T = ", "; end endmodule\n"},
    {"package r; task f(); localparam type T = ",
     "; endtask endpackage\nmodule top; endmodule\n"},
};

TEST(ScopeTypeRefParamElab, HierarchicalOperandIsReportedAndAMemberIsNot) {
  for (const Written& place : kWrittenPlaces) {
    for (bool hierarchical : {true, false}) {
      SCOPED_TRACE(place.open);
      SimFixture f;
      ElaborateSrc(std::string("module n; logic [4:0] v; endmodule\n"
                               "package q; struct packed { bit v; } s; "
                               "endpackage\n")
                       .append(place.open)
                       .append(hierarchical ? "type(top.i.v)" : "type(q::s.v)")
                       .append(place.close),
                   f);
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(), kHierarchical, 3, "6.23"),
                hierarchical);
      EXPECT_EQ(f.has_errors, hierarchical);
    }
  }
}

TEST(ScopeTypeRefParamElab, OperandThatNamesNothingIsReported) {
  for (const Written& place : kWrittenPlaces) {
    for (const char* operand :
         {"nosuch", "nosuch + 1", "-nosuch", "pk::w9 ? nosuch : 1",
          "{pk::w9, nosuch}", "{2{nosuch}}", "nosuch[0]", "pk::nosuch",
          "pk::nosuch + 1", "pk::nosuch[3:0]"}) {
      SCOPED_TRACE(place.open);
      SCOPED_TRACE(operand);
      SimFixture f;
      ElaborateSrc(std::string(kPackage)
                       .append(place.open)
                       .append("type(")
                       .append(operand)
                       .append(")")
                       .append(place.close),
                   f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "type parameter 'T' can only be set to a data "
                                "type, not a value expression",
                                12, "6.20.3"));
    }
  }
}

TEST(ScopeTypeRefParamElab, OperandThatNamesSomethingIsAccepted) {
  for (const Written& place : kWrittenPlaces) {
    for (const char* operand : {"logic [6:0]", "string",
                                "event",       "mailbox",
                                "semaphore",   "process",
                                "pk::t",       "pk::w9",
                                "-pk::w9",     "pk::w9 ? pk::w9 : 1",
                                "{2{pk::w9}}", "pk::w9[0]",
                                "pk::K",       "pk::K::t2",
                                "pk::K::sv",   "pk::K::N::t3",
                                "pk::s",       "pk::s + 1",
                                "pk::s.f",     "pk::s.f + 1"}) {
      SCOPED_TRACE(place.open);
      SCOPED_TRACE(operand);
      SimFixture f;
      ElaborateSrc(std::string(kPackage)
                       .append(place.open)
                       .append("type(")
                       .append(operand)
                       .append(")")
                       .append(place.close),
                   f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(ScopeTypeRefParamElab, OperandMayBeTheObjectItself) {
  SimFixture f;
  ElaborateSrc(
      "class W; localparam type T = type(this); endclass\n"
      "module top; W w; endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ScopeTypeRefParamElab, RestrictedParameterTakesOnlyTheKindItNames) {
  for (const Written& place : kWrittenPlaces) {
    for (bool conforming : {false, true}) {
      SCOPED_TRACE(place.open);
      std::string open(place.open);
      open.insert(open.find("type T") + 5, "enum ");
      SimFixture f;
      ElaborateSrc(std::string("package q; enum {A, B} e; bit v; endpackage\n")
                       .append(open)
                       .append(conforming ? "type(q::e)" : "type(q::v)")
                       .append(place.close),
                   f);
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "type parameter 'T' is assigned a type that does "
                              "not conform to the required enum kind",
                              2, "6.20.3"),
                !conforming);
      EXPECT_EQ(f.has_errors, !conforming);
    }
  }
}

TEST(ScopeTypeRefParamElab, OperandMayNameAnImplicitNet) {
  for (const char* declares : {"assign i = 1'b1;", "assign {j, i} = 2'b1;",
                               "buf (i, 1'b1);", "n u(i);", "n u(.p(i));"}) {
    for (const char* operand : {"i", "i + 1"}) {
      SCOPED_TRACE(declares);
      SimFixture f;
      ElaborateSrc(std::string("module n (output p); endmodule\n"
                               "module top;\n  ")
                       .append(declares)
                       .append("\n  class W; localparam type T = type(")
                       .append(operand)
                       .append("); endclass\nendmodule\n"),
                   f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

}  // namespace
