#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string AtTimeZero(const std::string& decls, const std::string& writes,
                       const std::string& shown, const std::string& args) {
  return "checker chk(logic clk);\n" + decls +
         "  m: assume property (@(posedge clk) clk);\n" + writes +
         "  initial a0: assert final (0) else $display(\"" + shown + "\", " +
         args +
         ");\n"
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  chk c(clk);\n"
         "  initial #12 $finish;\n"
         "endmodule\n";
}

std::string Shown(const std::string& out, const std::string& name) {
  std::string key = name + "=";
  size_t at = out.find(key);
  if (at == std::string::npos) return "";
  size_t end = out.find_first_of(" \n", at);
  return out.substr(at + key.size(), end - at - key.size());
}

uint64_t ShownNumber(const std::string& out, const std::string& name) {
  std::string text = Shown(out, name);
  EXPECT_FALSE(text.empty()) << name << " not shown in:\n" << out;
  return text.empty() ? 0 : std::stoull(text);
}

std::string RunDesign(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(FreeVariableInitialValue,
     DISABLED_AnActiveVariableStartsRandomOrAtItsInitializer) {
  std::string out =
      RunDesign(AtTimeZero("  rand bit [31:0] x;\n"
                           "  rand bit [31:0] y = 32'd123;\n",
                           "", "x=%0d y=%0d", "x, y"));
  EXPECT_NE(ShownNumber(out, "x"), 0u);
  EXPECT_EQ(ShownNumber(out, "y"), 123u);
}

TEST(FreeVariableInitialValue,
     AnInactiveVariableStartsRandomOrAtItsInitializer) {
  std::string out =
      RunDesign(AtTimeZero("  rand bit [31:0] x;\n"
                           "  rand bit [31:0] y = 32'd456;\n",
                           "  always_ff @(posedge clk) x <= 32'd1;\n"
                           "  always_ff @(posedge clk) y <= 32'd1;\n",
                           "x=%0d y=%0d", "x, y"));
  EXPECT_NE(ShownNumber(out, "x"), 0u);
  EXPECT_EQ(ShownNumber(out, "y"), 456u);
}

TEST(FreeVariableInitialValue, PartlyWrittenPackedVariablesStartRandom) {
  std::string out = RunDesign(
      AtTimeZero("  typedef struct packed { bit x; bit [31:0] q; } st_t;\n"
                 "  rand bit [31:0] s;\n"
                 "  rand st_t p;\n",
                 "  always_ff @(posedge clk) s[0] <= 1'b1;\n"
                 "  always_ff @(posedge clk) p.x <= 1'b1;\n",
                 "s=%0d p=%0d", "s[31:1], p.q"));
  EXPECT_NE(ShownNumber(out, "s"), 0u);
  EXPECT_NE(ShownNumber(out, "p"), 0u);
}

TEST(FreeVariableInitialValue, IntAndFourStateVariablesStartRandomAndKnown) {
  std::string out =
      RunDesign(AtTimeZero("  rand int i;\n"
                           "  rand logic [31:0] l;\n",
                           "", "i=%0d l=%b", "i, l"));
  EXPECT_NE(ShownNumber(out, "i"), 0u);
  std::string bits = Shown(out, "l");
  ASSERT_EQ(bits.size(), 32u) << out;
  EXPECT_EQ(bits.find_first_of("xXzZ"), std::string::npos) << bits;
  EXPECT_NE(bits.find('1'), std::string::npos) << bits;
}

TEST(FreeVariableInitialValue, EnumAndPackedStructureVariablesStartRandom) {
  std::string out = RunDesign(AtTimeZero(
      "  typedef enum bit [31:0] { A = 1, B = 2 } e_t;\n"
      "  typedef struct packed { bit [15:0] p; bit [15:0] q; } st_t;\n"
      "  rand e_t e;\n"
      "  rand st_t s;\n",
      "", "e=%0d s=%0d", "e, s"));
  EXPECT_NE(ShownNumber(out, "e"), 0u);
  EXPECT_NE(ShownNumber(out, "s"), 0u);
}

TEST(FreeVariableInitialValue, AnUnpackedStructureStartsRandom) {
  std::string out = RunDesign(
      AtTimeZero("  typedef struct { bit [31:0] p; bit [31:0] q; } us_t;\n"
                 "  rand us_t s;\n",
                 "", "p=%0d q=%0d", "s.p, s.q"));
  EXPECT_NE(ShownNumber(out, "p"), 0u);
  EXPECT_NE(ShownNumber(out, "q"), 0u);
}

TEST(FreeVariableInitialValue, DISABLED_AnActiveUnpackedArrayStartsRandom) {
  std::string out = RunDesign(AtTimeZero("  rand bit [31:0] u [2];\n", "",
                                         "u0=%0d u1=%0d", "u[0], u[1]"));
  EXPECT_NE(ShownNumber(out, "u0"), 0u);
  EXPECT_NE(ShownNumber(out, "u1"), 0u);
}

TEST(FreeVariableInitialValue, DISABLED_AConstantUnpackedArrayStartsRandom) {
  std::string out = RunDesign(AtTimeZero("  rand const bit [31:0] u [2];\n", "",
                                         "u0=%0d u1=%0d", "u[0], u[1]"));
  EXPECT_NE(ShownNumber(out, "u0"), 0u);
  EXPECT_NE(ShownNumber(out, "u1"), 0u);
}

TEST(FreeVariableInitialValue,
     DISABLED_APartlyWrittenUnpackedArrayStartsRandom) {
  std::string out =
      RunDesign(AtTimeZero("  rand bit [31:0] u [2];\n",
                           "  always_ff @(posedge clk) u[0] <= 32'd1;\n",
                           "u0=%0d u1=%0d", "u[0], u[1]"));
  EXPECT_NE(ShownNumber(out, "u0"), 0u);
  EXPECT_NE(ShownNumber(out, "u1"), 0u);
}

TEST(FreeVariableInitialValue, AnInitializedUnpackedArrayStartsAtIt) {
  std::string out =
      RunDesign(AtTimeZero("  rand bit [7:0] u [2] = '{8'd3, 8'd4};\n", "",
                           "u0=%0d u1=%0d", "u[0], u[1]"));
  EXPECT_EQ(ShownNumber(out, "u0"), 3u);
  EXPECT_EQ(ShownNumber(out, "u1"), 4u);
}

constexpr std::string_view kPlacedChecker =
    "checker chk(logic clk, int id);\n"
    "  rand bit [31:0] ua, ui;\n"
    "  rand bit [31:0] ii = 32'd789;\n"
    "  m: assume property (@(posedge clk) clk);\n"
    "  always_ff @(posedge clk) ui <= 32'd1;\n"
    "  initial a0: assert final (0)\n"
    "    else $display(\"id%0d ua=%0d ui=%0d ii=%0d\", id, ua, ui, ii);\n"
    "endchecker\n";

void ExpectPlacedStart(const std::string& out, int id) {
  std::string key = "id" + std::to_string(id) + " ";
  size_t at = out.find(key);
  ASSERT_NE(at, std::string::npos) << key << " not shown in:\n" << out;
  std::string line = out.substr(at, out.find('\n', at) - at);
  EXPECT_NE(ShownNumber(line, "ua"), 0u) << line;
  EXPECT_NE(ShownNumber(line, "ui"), 0u) << line;
  EXPECT_EQ(ShownNumber(line, "ii"), 789u) << line;
}

TEST(FreeVariableInitialValue,
     DISABLED_EveryInstantiationPlaceStartsTheSameWay) {
  std::string out = RunDesign(std::string(kPlacedChecker) +
                              "checker outer(logic clk);\n"
                              "  chk c(clk, 2);\n"
                              "endchecker\n"
                              "interface ifc(input logic clk);\n"
                              "  chk c(clk, 3);\n"
                              "endinterface\n"
                              "program pr(input logic clk);\n"
                              "  chk c(clk, 4);\n"
                              "endprogram\n"
                              "module top;\n"
                              "  logic clk = 0;\n"
                              "  always #5 clk = ~clk;\n"
                              "  chk c(clk, 1);\n"
                              "  outer o(clk);\n"
                              "  ifc i(clk);\n"
                              "  pr p(clk);\n"
                              "  initial #12 $finish;\n"
                              "endmodule\n");
  for (int id = 1; id <= 4; ++id) {
    SCOPED_TRACE(id);
    ExpectPlacedStart(out, id);
  }
}

TEST(FreeVariableInitialValue, DISABLED_AProceduralInstanceStartsTheSameWay) {
  std::string out = RunDesign(std::string(kPlacedChecker) +
                              "module top;\n"
                              "  logic clk = 0;\n"
                              "  always #5 clk = ~clk;\n"
                              "  always @(posedge clk) chk c(clk, 5);\n"
                              "  initial #12 $finish;\n"
                              "endmodule\n");
  ExpectPlacedStart(out, 5);
}

}  // namespace
