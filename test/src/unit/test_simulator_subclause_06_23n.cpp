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

constexpr std::string_view kShared =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n";

constexpr std::string_view kDeclarations =
    "class X #(type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v); endfunction\n"
    "endclass\n"
    "class Z #(int W = 1, type T = int);\n"
    "  T v;\n"
    "  function int w(); return $bits(v) * 10 + W; endfunction\n"
    "endclass\n"
    "interface class I #(type T = int);\n"
    "  pure virtual function int f(T x);\n"
    "endclass\n"
    "interface class V #(type T = int);\n"
    "endclass\n"
    "logic [6:0] n;\n"
    "localparam logic [2:0] L = 1;\n"
    "pk::K k;\n";

struct BasePlace {
  std::string_view open;
  std::string_view use;
  std::string_view close;
};

constexpr BasePlace kBasePlaces[] = {
    {"module top;\n", "", "endmodule\n"},
    {"interface itf;\n", "", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "", "endprogram\nmodule top; p i(); endmodule\n"},
    {"module top;\nif (1) begin : b\n", "", "end\nendmodule\n"},
    {"package q;\n", "endpackage\nmodule top;\nimport q::*;\n", "endmodule\n"},
    {"", "module top;\n", "endmodule\n"},
};

constexpr BasePlace kImplementerPlaces[] = {kBasePlaces[3], kBasePlaces[4],
                                            kBasePlaces[5]};

std::string Declared(const BasePlace& place) {
  return std::string(kShared).append(place.open).append(kDeclarations);
}

uint32_t LineAfter(const std::string& text) {
  return static_cast<uint32_t>(std::ranges::count(text, '\n') + 1);
}

void ExpectPrintedIn(std::span<const BasePlace> places,
                     std::string_view classes, std::string_view use,
                     std::string_view printed) {
  for (const BasePlace& place : places) {
    const std::string kSource =
        Declared(place).append(classes).append(place.use).append(use).append(
            place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSource, f), printed);
  }
}

void ExpectInEachBasePlace(std::string_view classes, std::string_view use,
                           std::string_view printed) {
  ExpectPrintedIn(kBasePlaces, classes, use, printed);
}

TEST(BaseTypeRefArgumentSim, ExtendsTakesEachOperand) {
  ExpectInEachBasePlace(
      "class A extends X #(type(n)); endclass\n"
      "class B extends X #(.T(type(n + 10'd0))); endclass\n"
      "class C extends X #(type(L)); endclass\n"
      "class D extends X #(type(pk::w9)); endclass\n"
      "class E extends X #(.T(type(pk::t))); endclass\n"
      "class F extends X #(type(logic [5:0])); endclass\n"
      "class G extends Z #(3, type(n)); endclass\n"
      "class H extends Z #(.T(type(L)), .W(4)); endclass\n"
      "class M extends X #(type(k)); endclass\n",
      "A a = new;\n"
      "B b = new;\n"
      "C c = new;\n"
      "D d = new;\n"
      "E e = new;\n"
      "F g = new;\n"
      "G h = new;\n"
      "H i = new;\n"
      "M m = new;\n"
      "pk::K o = new;\n"
      "initial begin\n"
      "  m.v = o;\n"
      "  $display(\"%0d %0d %0d %0d\", a.w(), $bits(a.v), b.w(), c.w());\n"
      "  $display(\"%0d %0d %0d %0d %0d %0d\", d.w(), e.w(), g.w(), h.w(),\n"
      "           i.w(), m.v.m);\n"
      "end\n",
      "7 7 10 3\n9 12 6 73 34 5\n");
}

TEST(BaseTypeRefArgumentSim, ObjectIsOneOfTheSpecializationTheOperandGives) {
  ExpectInEachBasePlace(
      "class A extends X #(type(n)); endclass\n"
      "class B extends A; endclass\n",
      "B b = new;\n"
      "X #(logic [6:0]) x;\n"
      "initial begin\n"
      "  x = b;\n"
      "  $display(\"%0d %0d\", b.w(), x.w());\n"
      "end\n",
      "7 7\n");
}

TEST(BaseTypeRefArgumentSim, NestedClassExtends) {
  ExpectInEachBasePlace(
      "class O;\n"
      "  class D extends X #(type(n)); endclass\n"
      "  D d = new;\n"
      "endclass\n",
      "O o = new;\n"
      "initial $display(\"%0d\", o.d.w());\n",
      "7\n");
}

TEST(BaseTypeRefArgumentSim, OperandIsNoPropertyTheClassDeclares) {
  ExpectInEachBasePlace(
      "class D extends X #(type(n)); logic [1:0] n; endclass\n",
      "D d = new;\n"
      "initial $display(\"%0d %0d\", d.w(), $bits(d.n));\n",
      "7 2\n");
}

TEST(BaseTypeRefArgumentSim, OperandIsTheClassesOwnParameter) {
  ExpectInEachBasePlace(
      "class A #(type T = logic [3:0]) extends X #(type(T)); endclass\n"
      "class B #(int W = 3, logic [W-1:0] P = 0) extends X #(type(P));\n"
      "endclass\n"
      "class C #(byte W = 3) extends X #(type(W)); endclass\n",
      "A a = new;\n"
      "A #(logic [8:0]) b = new;\n"
      "B c = new;\n"
      "B #(5) d = new;\n"
      "C e = new;\n"
      "initial $display(\"%0d %0d %0d %0d %0d\", a.w(), b.w(), c.w(), d.w(),\n"
      "                 e.w());\n",
      "4 9 3 5 8\n");
}

TEST(BaseTypeRefArgumentSim, ImplementsTakesEachOperand) {
  ExpectPrintedIn(
      kImplementerPlaces,
      "class A implements I #(type(n));\n"
      "  virtual function int f(logic [6:0] x); return $bits(x); endfunction\n"
      "endclass\n"
      "class B implements I #(.T(type(n + 10'd0)));\n"
      "  virtual function int f(logic [9:0] x); return $bits(x); endfunction\n"
      "endclass\n"
      "class C implements I #(type(L));\n"
      "  virtual function int f(logic [2:0] x); return $bits(x); endfunction\n"
      "endclass\n"
      "class D implements I #(type(pk::w9));\n"
      "  virtual function int f(logic [8:0] x); return $bits(x); endfunction\n"
      "endclass\n"
      "class E implements I #(type(pk::t));\n"
      "  virtual function int f(pk::t x); return $bits(x); endfunction\n"
      "endclass\n"
      "class F implements I #(type(logic [5:0]));\n"
      "  virtual function int f(logic [5:0] x); return $bits(x); endfunction\n"
      "endclass\n"
      "class G implements I #(type(k));\n"
      "  virtual function int f(pk::K x); return x.m; endfunction\n"
      "endclass\n",
      "A a = new;\n"
      "B b = new;\n"
      "C c = new;\n"
      "D d = new;\n"
      "E e = new;\n"
      "F g = new;\n"
      "G h = new;\n"
      "pk::K o = new;\n"
      "I #(logic [6:0]) i;\n"
      "initial begin\n"
      "  i = a;\n"
      "  $display(\"%0d %0d %0d %0d\", i.f(1), b.f(1), c.f(1), d.f(1));\n"
      "  $display(\"%0d %0d %0d\", e.f(1), g.f(1), h.f(o));\n"
      "end\n",
      "7 10 3 9\n12 6 5\n");
}

TEST(BaseTypeRefArgumentSim, InterfaceClassExtends) {
  ExpectPrintedIn(
      kImplementerPlaces,
      "interface class J extends I #(type(n)); endclass\n"
      "class D implements J;\n"
      "  virtual function int f(logic [6:0] x); return $bits(x); endfunction\n"
      "endclass\n",
      "D d = new;\n"
      "J j;\n"
      "I #(logic [6:0]) i;\n"
      "initial begin\n"
      "  j = d;\n"
      "  i = d;\n"
      "  $display(\"%0d %0d\", j.f(1), i.f(1));\n"
      "end\n",
      "7 7\n");
}

constexpr std::string_view kBases[] = {
    "class D extends X #(type(@)); endclass\n",
    "class D extends X #(.T(type(@))); endclass\n",
    "class D implements V #(type(@)); endclass\n",
    "interface class D extends V #(type(@)); endclass\n",
};

void ExpectBaseOperandsJudged(const BasePlace& place, std::string_view base) {
  for (std::string_view operand : {"pk::w9", "nosuch", "top.u.hv"}) {
    std::string text(base);
    text.replace(text.find('@'), 1, operand);
    const std::string kBefore = Declared(place);
    const std::string kSource =
        std::string(kBefore).append(text).append(place.use).append(place.close);
    SCOPED_TRACE(kSource);
    SimFixture f;
    ElaborateSrc(kSource, f);
    const uint32_t kLine = LineAfter(kBefore);
    const std::string_view kClass = base.find("X #") == base.npos ? "V" : "X";
    EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                            std::string("parameter value assignment for type "
                                        "parameter 'T' of '")
                                .append(kClass)
                                .append("' does not name a type"),
                            kLine, "6.20.3"),
              operand == "nosuch");
    EXPECT_EQ(
        ReportedError(f.diag.Diagnostics(),
                      "type operator argument uses a hierarchical reference, "
                      "which the type operator does not accept",
                      kLine, "6.23"),
        operand == "top.u.hv");
    EXPECT_EQ(f.diag.Diagnostics().size(), operand == "pk::w9" ? 0U : 1U);
  }
}

TEST(BaseTypeRefArgumentElab, OperandNamesATypeWithoutAHierarchicalName) {
  for (const BasePlace& place : kBasePlaces) {
    for (std::string_view base : kBases) ExpectBaseOperandsJudged(place, base);
  }
}

TEST(BaseTypeRefArgumentElab, OwnValueParameterNamesNoType) {
  for (const BasePlace& place : kBasePlaces) {
    for (std::string_view argument : {"type(P)", "P"}) {
      const std::string kBefore = Declared(place);
      const std::string kSource =
          std::string(kBefore)
              .append("class D #(int P = 1) extends X #(")
              .append(argument)
              .append("); endclass\n")
              .append(place.use)
              .append(place.close);
      SCOPED_TRACE(kSource);
      SimFixture f;
      ElaborateSrc(kSource, f);
      EXPECT_EQ(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of 'X' does not name a type",
                              LineAfter(kBefore), "6.20.3"),
                argument == "P");
      EXPECT_EQ(f.diag.Diagnostics().size(), argument == "P" ? 1U : 0U);
    }
  }
}

}  // namespace
