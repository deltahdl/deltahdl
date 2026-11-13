#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string TypedSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic [7:0] v;\n"
         "  logic w, go, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign v = (tick inside {2, 4}) ? 8'h02\n"
         "           : (tick inside {6}) ? 8'h01 : 8'h00;\n"
         "  assign w = tick inside {2, 6};\n"
         "  assign go = tick inside {1, 3, 5, 7};\n"
         "  assign b = tick inside {2, 3, 6, 7, 8};\n"
         "  assign c = tick inside {2, 4};\n"
         "  property p_untyped(x, y);\n"
         "    @(posedge clk) x |-> y;\n"
         "  endproperty\n"
         "  property p_bit(bit x, y);\n"
         "    @(posedge clk) x |-> y;\n"
         "  endproperty\n"
         "  property p_ev(event ev);\n"
         "    @(ev) v == 2 |-> w;\n"
         "  endproperty\n"
         "  property p_prop(property q);\n"
         "    @(posedge clk) go |-> q;\n"
         "  endproperty\n"
         "  property p_not(property q);\n"
         "    @(posedge clk) not q;\n"
         "  endproperty\n"
         "  property p_id(property q);\n"
         "    @(posedge clk) q;\n"
         "  endproperty\n"
         "  property p_not_or(property q);\n"
         "    @(posedge clk) not q or 1'b0;\n"
         "  endproperty\n"
         "  property p_seq(sequence s);\n"
         "    @(posedge clk) s |-> c;\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

std::pair<uint64_t, uint64_t> CountsOfTyped(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(TypedSource("  p: assert property (" + spec +
                                           ") passes++; else fails++;\n"),
                               f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  return {passes->value.ToUint64(), fails->value.ToUint64()};
}

TEST(TypedPropertyFormals, ADataTypedFormalCastsItsActual) {
  auto untyped = CountsOfTyped("p_untyped(v, w)");
  EXPECT_EQ(untyped.first, 7u);
  EXPECT_EQ(untyped.second, 1u);
  auto typed = CountsOfTyped("p_bit(v, w)");
  EXPECT_EQ(typed.first, 8u);
  EXPECT_EQ(typed.second, 0u);
}

TEST(TypedPropertyFormals, AnEventFormalTakesTheInstancesEvent) {
  auto counts = CountsOfTyped("p_ev(posedge clk)");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(TypedPropertyFormals, AnOrOrIffEventActualIsTheWrittenClock) {
  EXPECT_EQ(CountsOfTyped("p_ev(negedge clk or posedge clk)"),
            CountsOfTyped("@(negedge clk or posedge clk) v == 2 |-> w"));
  EXPECT_EQ(CountsOfTyped("p_ev(posedge clk iff go)"),
            CountsOfTyped("@(posedge clk iff go) v == 2 |-> w"));
}

TEST(TypedPropertyFormals, ThreeEventActualsOfOnePropertyRun) {
  SimFixture f;
  Variable* a = RunAndFindVar(
      "module top; logic clk, a;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(posedge clk, a));\n"
      "  a2: assert property (p(negedge clk or posedge clk, a));\n"
      "  a3: assert property (p(posedge clk iff a, a));\n"
      "endmodule\n",
      f, "a");
  EXPECT_NE(a, nullptr);
}

TEST(TypedPropertyFormals, ABooleanMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b)");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(TypedPropertyFormals, ASequenceMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b ##1 c)");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

TEST(TypedPropertyFormals, APropertyMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b or nexttime c)");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(TypedPropertyFormals, APropertyFormalMayStandUnderNot) {
  auto counts = CountsOfTyped("p_not(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

TEST(TypedPropertyFormals, APropertyFormalUnderNotAfterAClock) {
  auto counts = CountsOfTyped("@(posedge clk) p_not(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

TEST(TypedPropertyFormals, APropertyFormalMayBeTheWholeBody) {
  auto counts = CountsOfTyped("p_id(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

TEST(TypedPropertyFormals, APropertyFormalUnderNotInAPropertyOfOperands) {
  auto counts = CountsOfTyped("p_not_or(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

TEST(TypedPropertyFormals, ASequenceFormalMayStandAsAnAntecedent) {
  auto counts = CountsOfTyped("p_seq(go ##1 b)");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

std::pair<uint64_t, uint64_t> CountsWithDeclaration(
    const std::string& declaration, const std::string& spec) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(TypedSource(declaration + "  p: assert property (" + spec +
                                ") passes++; else fails++;\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  return {passes->value.ToUint64(),
          f.ctx.FindVariable("fails")->value.ToUint64()};
}

TEST(TypedPropertyFormals,
     DISABLED_ADefaultActualOfAPropertyFormalRunsAsIfWritten) {
  const std::string kDeclaration =
      "  property p_def(property q = b ##1 c); @(posedge clk) q; "
      "endproperty\n";
  auto defaulted = CountsWithDeclaration(kDeclaration, "p_def");
  EXPECT_EQ(defaulted, CountsOfTyped("p_id(b ##1 c)"));
  EXPECT_EQ(defaulted, CountsWithDeclaration(kDeclaration, "p_def(b ##1 c)"));
  EXPECT_NE(defaulted, CountsWithDeclaration(kDeclaration, "p_def(c)"));
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedTypedProperties =
    "  property pp(property q); q; endproperty\n"
    "  property pn(property q); not q; endproperty\n"
    "  property ps(sequence s); s |-> d; endproperty\n"
    "  property pe(event e, property q); @(e) q; endproperty\n"
    "  property pb(bit x, y); x |-> y; endproperty\n";

const PlacedProperty kTypedFormalsInPlace[] = {
    {"pp(d)", {3, 1}, 3},
    {"pp(a ##1 b)", {1, 3}, 1},
    {"pp(c or nexttime a)", {2, 2}, 2},
    {"pp(@(posedge clk) a)", {2, 2}, 2},
    {"pp(.q(a ##1 b))", {1, 3}, 1},
    {"pn(b)", {2, 2}, 2},
    {"ps(a ##1 b)", {4, 0}, 4},
    {"pb(c, d)", {3, 1}, 3},
    {"pb(2'b10, d)", {4, 0}, 4}};

TEST(TypedPropertyFormals, ATypedFormalCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kTypedFormalsInPlace) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedTypedProperties);
    }
  }
}

TEST(TypedPropertyFormals,
     DISABLED_AnEventFormalClocksItsBodyUnderALeadingClockInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    ExpectPropertyCountsInPlace(place, {"pe(posedge clk, d)", {3, 1}, 3},
                                kPlacedStimulus, kPlacedTypedProperties);
  }
}

TEST(TypedPropertyFormals,
     DISABLED_ATypedFormalCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kTypedFormalsInPlace) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedTypedProperties);
  }
}

}  // namespace
