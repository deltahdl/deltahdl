#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& units, const std::string& items,
                   int end) {
  return units + "checker chk(int b, logic clk);\n" + items +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  int b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) b = b + 1;\n"
         "  chk c(b, clk);\n"
         "  initial #" +
         std::to_string(end) +
         " $finish;\n"
         "endmodule\n";
}

std::string Tracks(const std::string& b) { return "16'(b) + 16'd" + b; }

std::string Assumes(const std::string& label, const std::string& target,
                    const std::string& offset) {
  return "  " + label + ": assume property (@(posedge clk) " + target +
         " == " + Tracks(offset) + ");\n";
}

std::string CountsChanges(const std::string& name, const std::string& expr,
                          const std::string& type = "bit [15:0]") {
  return "  int " + name + " = 0;\n  " + type + " " + name +
         "_last;\n"
         "  always_ff @(posedge clk) begin\n"
         "    if (" +
         expr + " != " + name + "_last) " + name + " <= " + name +
         " + 1;\n"
         "    " +
         name + "_last <= " + expr +
         ";\n"
         "  end\n";
}

std::string Copies(const std::string& name, const std::string& expr) {
  return "  bit [15:0] " + name + ";\n  always_ff @(posedge clk) " + name +
         " <= " + expr + ";\n";
}

constexpr std::string_view kEmptyAssumeSet =
    "  m: assume property (@(posedge clk) clk);\n";

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

void RunDesign(SimFixture& f, const std::string& src, std::string_view first) {
  ASSERT_NE(RunAndFindVar(src, f, first), nullptr);
}

TEST(UnpackedFreeVariableActiveness,
     PackedBitsAndMembersNotWrittenAreNotRedrawn) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  typedef struct packed { bit x; bit [14:0] q; } st_t;\n"
                   "  rand bit [15:0] s;\n"
                   "  rand st_t p;\n" +
                       std::string(kEmptyAssumeSet) +
                       "  always_ff @(posedge clk) s[0] <= !s[0];\n"
                       "  always_ff @(posedge clk) p.x <= !p.x;\n" +
                       CountsChanges("sc", "s[15:1]", "bit [14:0]") +
                       CountsChanges("pc", "p.q", "bit [14:0]"),
                   202),
            "c.sc");
  EXPECT_LE(ValueOf(f, "c.sc"), 1u);
  EXPECT_LE(ValueOf(f, "c.pc"), 1u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_APackedMemberAndAPartSelectAreSolvedForTheirAssumptions) {
  SimFixture f;
  RunDesign(
      f,
      Design("",
             "  typedef struct packed { bit [15:0] p; bit [15:0] q; } st_t;\n"
             "  rand st_t s;\n"
             "  rand bit [31:0] w;\n" +
                 Assumes("m1", "s.q", "200") + Assumes("m2", "w[15:0]", "300") +
                 Copies("cq", "s.q") + Copies("cw", "w[15:0]"),
             42),
      "c.cq");
  EXPECT_EQ(ValueOf(f, "c.cq"), 203u);
  EXPECT_EQ(ValueOf(f, "c.cw"), 303u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_EachUnwrittenElementIsSolvedOnItsOwn) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] u [2];\n" + Assumes("m0", "u[0]", "100") +
                       Assumes("m1", "u[1]", "200") + Copies("c0", "u[0]") +
                       Copies("c1", "u[1]"),
                   42),
            "c.c0");
  EXPECT_EQ(ValueOf(f, "c.c0"), 103u);
  EXPECT_EQ(ValueOf(f, "c.c1"), 203u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_EachUnwrittenElementIsRedrawnWithAnEmptyAssumeSet) {
  SimFixture f;
  RunDesign(
      f,
      Design("",
             "  rand bit [15:0] u [2];\n" + std::string(kEmptyAssumeSet) +
                 CountsChanges("n0", "u[0]") + CountsChanges("n1", "u[1]"),
             202),
      "c.n0");
  EXPECT_GT(ValueOf(f, "c.n0"), 10u);
  EXPECT_GT(ValueOf(f, "c.n1"), 10u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AWrittenElementKeepsItsValuesBesideASolvedOne) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] u [2];\n"
                   "  always_ff @(posedge clk) u[0] <= 16'd77;\n" +
                       Assumes("m1", "u[1]", "200") + Copies("c0", "u[0]") +
                       Copies("c1", "u[1]"),
                   42),
            "c.c0");
  EXPECT_EQ(ValueOf(f, "c.c0"), 77u);
  EXPECT_EQ(ValueOf(f, "c.c1"), 203u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AnUnwrittenElementBesideAWrittenOneIsRedrawn) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] u [2];\n"
                   "  always_ff @(posedge clk) u[0] <= 16'd77;\n" +
                       std::string(kEmptyAssumeSet) +
                       CountsChanges("n1", "u[1]") + Copies("c0", "u[0]"),
                   202),
            "c.n1");
  EXPECT_GT(ValueOf(f, "c.n1"), 10u);
  EXPECT_EQ(ValueOf(f, "c.c0"), 77u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AnElementWrittenThroughAConcatenationAloneIsInactive) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] u [2];\n"
                   "  bit z;\n"
                   "  always_ff @(posedge clk) {u[0], z} <= {16'd77, 1'b1};\n" +
                       Assumes("m1", "u[1]", "200") + Copies("c0", "u[0]") +
                       Copies("c1", "u[1]"),
                   42),
            "c.c0");
  EXPECT_EQ(ValueOf(f, "c.c0"), 77u);
  EXPECT_EQ(ValueOf(f, "c.c1"), 203u);
}

constexpr std::string_view kUnpackedStructure =
    "  typedef struct { bit [15:0] p; bit [15:0] q; } us_t;\n"
    "  rand us_t s;\n";

TEST(UnpackedFreeVariableActiveness,
     DISABLED_EachUnwrittenMemberIsSolvedOnItsOwn) {
  SimFixture f;
  RunDesign(
      f,
      Design("",
             std::string(kUnpackedStructure) + Assumes("m0", "s.p", "100") +
                 Assumes("m1", "s.q", "200") + Copies("cp", "s.p") +
                 Copies("cq", "s.q"),
             42),
      "c.cp");
  EXPECT_EQ(ValueOf(f, "c.cp"), 103u);
  EXPECT_EQ(ValueOf(f, "c.cq"), 203u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AMemberBesideAWrittenOneIsSolvedAndRedrawn) {
  SimFixture solved;
  RunDesign(solved,
            Design("",
                   std::string(kUnpackedStructure) +
                       "  always_ff @(posedge clk) s.p <= 16'd77;\n" +
                       Assumes("m1", "s.q", "200") + Copies("cp", "s.p") +
                       Copies("cq", "s.q"),
                   42),
            "c.cp");
  EXPECT_EQ(ValueOf(solved, "c.cp"), 77u);
  EXPECT_EQ(ValueOf(solved, "c.cq"), 203u);
  SimFixture drawn;
  RunDesign(
      drawn,
      Design("",
             std::string(kUnpackedStructure) +
                 "  always_ff @(posedge clk) s.p <= 16'd77;\n" +
                 std::string(kEmptyAssumeSet) + CountsChanges("nq", "s.q"),
             202),
      "c.nq");
  EXPECT_GT(ValueOf(drawn, "c.nq"), 10u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AMultidimensionalArraySolvesEachUnwrittenElement) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] u [2][2];\n"
                   "  always_ff @(posedge clk) u[0][0] <= 16'd77;\n" +
                       Assumes("m1", "u[0][1]", "100") +
                       Assumes("m2", "u[1][0]", "200") +
                       Assumes("m3", "u[1][1]", "300") +
                       Copies("c00", "u[0][0]") + Copies("c01", "u[0][1]") +
                       Copies("c10", "u[1][0]") + Copies("c11", "u[1][1]"),
                   42),
            "c.c00");
  EXPECT_EQ(ValueOf(f, "c.c00"), 77u);
  EXPECT_EQ(ValueOf(f, "c.c01"), 103u);
  EXPECT_EQ(ValueOf(f, "c.c10"), 203u);
  EXPECT_EQ(ValueOf(f, "c.c11"), 303u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AMemberWriteMakesItsWholePackedElementInactive) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  typedef struct packed { bit x; bit [15:0] q; } st_t;\n"
                   "  rand st_t a [2];\n"
                   "  always_ff @(posedge clk) a[0].x <= !a[0].x;\n" +
                       Assumes("m0", "a[0].q", "100") +
                       Assumes("m1", "a[1].q", "200") + Copies("c1", "a[1].q") +
                       CountsChanges("n0", "a[0].q"),
                   42),
            "c.c1");
  EXPECT_EQ(ValueOf(f, "c.c1"), 203u);
  EXPECT_LE(ValueOf(f, "c.n0"), 1u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_ABitWriteMakesItsPackedMemberAloneInactive) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  typedef struct { bit [15:0] v; bit [15:0] q; } us_t;\n"
                   "  rand us_t s;\n"
                   "  always_ff @(posedge clk) s.v[0] <= !s.v[0];\n" +
                       std::string(kEmptyAssumeSet) +
                       CountsChanges("nv", "s.v[15:1]", "bit [14:0]") +
                       CountsChanges("nq", "s.q"),
                   202),
            "c.nv");
  EXPECT_LE(ValueOf(f, "c.nv"), 1u);
  EXPECT_GT(ValueOf(f, "c.nq"), 10u);
}

TEST(UnpackedFreeVariableActiveness, ConstantUnpackedVariablesAreNeverDrawn) {
  SimFixture f;
  RunDesign(
      f,
      Design("",
             "  typedef struct { bit [15:0] p; bit [15:0] q; } us_t;\n"
             "  rand const bit [15:0] u [2];\n"
             "  rand const us_t s;\n" +
                 std::string(kEmptyAssumeSet) + CountsChanges("n0", "u[0]") +
                 CountsChanges("n1", "u[1]") + CountsChanges("np", "s.p") +
                 CountsChanges("nq", "s.q"),
             202),
      "c.n0");
  for (std::string_view name : {"c.n0", "c.n1", "c.np", "c.nq"}) {
    EXPECT_LE(ValueOf(f, name), 1u) << name;
  }
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AScalarSharingAnAssumptionWithAnElementIsSolved) {
  SimFixture f;
  RunDesign(f,
            Design("",
                   "  rand bit [15:0] r, u [2];\n"
                   "  m1: assume property (@(posedge clk)\n"
                   "    r == " +
                       Tracks("300") + " && u[1] == " + Tracks("200") + ");\n" +
                       Copies("cr", "r") + Copies("c1", "u[1]"),
                   42),
            "c.cr");
  EXPECT_EQ(ValueOf(f, "c.cr"), 303u);
  EXPECT_EQ(ValueOf(f, "c.c1"), 203u);
}

TEST(UnpackedFreeVariableActiveness,
     DISABLED_AGenerateBlockAndAChildCheckerSolveEachElement) {
  SimFixture f;
  RunDesign(f,
            Design("checker kid(int b, logic clk);\n"
                   "  rand bit [15:0] u [2];\n"
                   "  always_ff @(posedge clk) u[0] <= 16'd77;\n" +
                       Assumes("m1", "u[1]", "200") + Copies("c0", "u[0]") +
                       Copies("c1", "u[1]") + "endchecker\n",
                   "  if (1) begin : g\n"
                   "    rand bit [15:0] u [2];\n"
                   "    always_ff @(posedge clk) u[0] <= 16'd77;\n" +
                       Assumes("m1", "u[1]", "200") + Copies("c0", "u[0]") +
                       Copies("c1", "u[1]") +
                       "  end\n"
                       "  kid k(b, clk);\n",
                   42),
            "c.g.c0");
  for (std::string_view scope : {"c.g", "c.k"}) {
    SCOPED_TRACE(scope);
    EXPECT_EQ(ValueOf(f, std::string(scope) + ".c0"), 77u);
    EXPECT_EQ(ValueOf(f, std::string(scope) + ".c1"), 203u);
  }
}

}  // namespace
