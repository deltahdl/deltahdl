#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::vector<uint64_t> Read(const std::string& src,
                           const std::vector<std::string>& names) {
  SimFixture f;
  std::vector<uint64_t> values;
  values.reserve(names.size());
  if (RunAndFindVar(src, f, names.front()) == nullptr) return values;
  for (const auto& name : names) {
    auto* var = f.ctx.FindVariable(name);
    values.push_back(var == nullptr ? 99 : var->value.ToUint64());
  }
  return values;
}

std::string Clocked(const std::string& cu, const std::string& items) {
  std::string src = cu;
  src += "checker chk(logic clk, sclk);\n";
  src += items;
  src +=
      "endchecker\n"
      "program drv;\n"
      "  initial begin\n"
      "    #0 top.sclk = 1;\n"
      "    #60;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk = 0, sclk = 0;\n"
      "  drv d();\n"
      "  initial #5 forever begin\n"
      "    clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5;\n"
      "  end\n"
      "  chk c(clk, sclk);\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  return src;
}

TEST(CheckerVariableLifetimeRuns, AGenerateBlockOrStaticVariableKeepsItsValue) {
  EXPECT_EQ(Read(Clocked("",
                         "  static int unsigned scnt = 0;\n"
                         "  always_ff @(posedge clk) scnt <= scnt + 1;\n"
                         "  if (1) begin : g\n"
                         "    int unsigned cnt = 0;\n"
                         "    always_ff @(posedge clk) cnt <= cnt + 1;\n"
                         "  end\n"),
                 {"c.scnt", "c.g.cnt"}),
            (std::vector<uint64_t>{5, 5}));
}

const char* const kChild =
    "checker child(logic clk, bit [7:0] q);\n"
    "  m: assume property (@(posedge clk) q == 8'd46);\n"
    "endchecker\n";

const char* const kTypes =
    "typedef enum logic [1:0] {E0, E1, E2, E3} e_t;\n"
    "typedef struct packed { bit [3:0] h, l; } pair_t;\n";

TEST(CheckerFreeVariableRuns, AFreeVariableOfEachTypeIsSolved) {
  EXPECT_EQ(
      Read(Clocked(kTypes,
                   "  rand logic [3:0] l;\n"
                   "  rand int i;\n"
                   "  rand e_t e;\n"
                   "  rand pair_t p;\n"
                   "  rand var logic [7:0] v;\n"
                   "  m1: assume property (@(posedge clk) l == 4'd9 && "
                   "i == 1234 && e == E2 && p == 8'h5a && v == 8'hc3);\n"),
           {"c.l", "c.i", "c.e", "c.p", "c.v"}),
      (std::vector<uint64_t>{9, 1234, 2, 0x5a, 0xc3}));
}

TEST(CheckerFreeVariableRuns, BothDeclaratorsOfOneDeclarationAreFree) {
  EXPECT_EQ(Read(Clocked("",
                         "  rand bit [7:0] a = 8'd0, b;\n"
                         "  m1: assume property (@(posedge clk) a == 8'd21 && "
                         "b == 8'd22);\n"),
                 {"c.a", "c.b"}),
            (std::vector<uint64_t>{21, 22}));
}

TEST(CheckerFreeVariableRuns,
     DISABLED_AFreeVariableInEachGenerateBlockIsSolved) {
  EXPECT_EQ(
      Read(Clocked(kChild,
                   "  if (1) begin : g\n"
                   "    rand bit [7:0] r;\n"
                   "    m: assume property (@(posedge clk) r == 8'd42);\n"
                   "  end\n"
                   "  for (genvar k = 0; k < 2; k++) begin : h\n"
                   "    rand bit [7:0] r;\n"
                   "    m: assume property (@(posedge clk) r == 8'd10 + k);\n"
                   "  end\n"
                   "  case (1)\n"
                   "    1: begin : k\n"
                   "      rand bit [7:0] r;\n"
                   "      m: assume property (@(posedge clk) r == 8'd43);\n"
                   "    end\n"
                   "  endcase\n"
                   "  generate\n"
                   "    rand bit [7:0] gr;\n"
                   "    mg: assume property (@(posedge clk) gr == 8'd44);\n"
                   "  endgenerate\n"
                   "  if (1) begin : o\n"
                   "    if (1) begin : n\n"
                   "      rand bit [7:0] r;\n"
                   "      m: assume property (@(posedge clk) r == 8'd45);\n"
                   "    end\n"
                   "  end\n"
                   "  if (1) begin : b\n"
                   "    rand bit [7:0] r;\n"
                   "    child u(clk, r);\n"
                   "  end\n"),
           {"c.g.r", "c.h[0].r", "c.h[1].r", "c.k.r", "c.gr", "c.o.n.r",
            "c.b.r"}),
      (std::vector<uint64_t>{42, 10, 11, 43, 44, 45, 46}));
}

TEST(CheckerFreeVariableRuns, DISABLED_AGenerateBlockFreeVariableStartsRandom) {
  EXPECT_EQ(Read(Clocked("",
                         "  if (1) begin : g\n"
                         "    rand bit [31:0] gv;\n"
                         "    rand logic [7:0] gl;\n"
                         "    rand const bit [31:0] gk;\n"
                         "    rand const bit [7:0] g7 = 8'd7;\n"
                         "    bit [31:0] first_gk = 0;\n"
                         "    int zero = 0, unknown = 0, moved = 0;\n"
                         "    always_ff @(posedge sclk) begin\n"
                         "      first_gk <= gk;\n"
                         "      if (gv == 0) zero <= zero + 1;\n"
                         "      if ($isunknown(gl)) unknown <= unknown + 1;\n"
                         "    end\n"
                         "    always_ff @(posedge clk) begin\n"
                         "      if (gk != first_gk) moved <= moved + 1;\n"
                         "      if (gk == 0) zero <= zero + 1;\n"
                         "    end\n"
                         "  end\n"),
                 {"c.g.zero", "c.g.unknown", "c.g.moved", "c.g.g7"}),
            (std::vector<uint64_t>{0, 0, 0, 7}));
}

std::string Held(const std::string& decl, const std::string& expr,
                 const std::string& init) {
  std::string items = decl;
  items +=
      "  bit [63:0] first = 0;\n"
      "  int changes = 0;\n"
      "  always_ff @(posedge sclk) first <= 64'(";
  items += expr;
  items += ");\n  always_ff @(posedge clk) if (";
  items += expr;
  items += " != ";
  items += init;
  items += ") changes <= changes + 1;\n";
  return items;
}

std::string Assumed(const std::string& decl, const std::string& expr,
                    const std::string& init) {
  std::string assumed = decl;
  assumed += "  m1: assume property (@(posedge clk) ";
  assumed += expr;
  assumed += " != ";
  assumed += init;
  assumed += ");\n";
  return Held(assumed, expr, init);
}

std::vector<uint64_t> FirstAndMoved(const std::string& src,
                                    const std::string& scope) {
  auto values = Read(src, {scope + ".first", scope + ".changes"});
  if (values.size() == 2) values[1] = values[1] > 0 ? 1 : 0;
  return values;
}

const char* const kHeldDecl = "  rand bit [15:0] a = 16'h1234, b;\n";

TEST(CheckerInitializedFreeVariable, ItHoldsItsInitializerAtTimeZeroOnly) {
  EXPECT_EQ(
      FirstAndMoved(
          Clocked("", Held(std::string(kHeldDecl) +
                               "  m1: assume property (@(posedge clk) a != "
                               "16'h0001);\n",
                           "a", "16'h1234")),
          "c"),
      (std::vector<uint64_t>{0x1234, 1}));
}

TEST(CheckerInitializedFreeVariable,
     DISABLED_AClockEventAtTimeZeroLeavesItHeld) {
  EXPECT_EQ(
      FirstAndMoved(
          Clocked("", Held(std::string(kHeldDecl) +
                               "  m0: assume property (@(posedge sclk) a != "
                               "16'h0001);\n"
                               "  m1: assume property (@(posedge clk) a != "
                               "16'h0002);\n",
                           "a", "16'h1234")),
          "c"),
      (std::vector<uint64_t>{0x1234, 1}));
}

TEST(CheckerInitializedFreeVariable,
     DISABLED_AnEmptyAssumeSetLeavesItHeldAtTimeZero) {
  EXPECT_EQ(FirstAndMoved(Clocked("", Held(kHeldDecl, "a", "16'h1234")), "c"),
            (std::vector<uint64_t>{0x1234, 1}));
}

struct HeldForm {
  const char* name;
  const char* decl;
  const char* expr;
  const char* init;
  uint64_t first;
};

void ExpectEachHeld(const std::vector<HeldForm>& forms) {
  for (const auto& form : forms) {
    SCOPED_TRACE(form.name);
    EXPECT_EQ(FirstAndMoved(Clocked(std::string(kTypes) +
                                        "package q;\n"
                                        "  parameter bit [3:0] P = 4'd9;\n"
                                        "endpackage\n",
                                    Assumed(form.decl, form.expr, form.init)),
                            "c"),
              (std::vector<uint64_t>{form.first, 1}));
  }
}

TEST(CheckerInitializedFreeVariable, EachTypeAndInitializerIsHeld) {
  ExpectEachHeld({
      {"logic", "  rand logic [7:0] a = 8'h5c;\n", "a", "8'h5c", 0x5c},
      {"int", "  rand int a = 5;\n", "a", "5", 5},
      {"enum", "  rand e_t a = E2;\n", "a", "E2", 2},
      {"packed struct", "  rand pair_t a = 8'h3c;\n", "a", "8'h3c", 0x3c},
      {"package parameter", "  rand bit [3:0] a = q::P;\n", "a", "q::P", 9},
  });
}

TEST(CheckerInitializedFreeVariable, DISABLED_AnUnpackedElementIsHeld) {
  ExpectEachHeld({
      {"unpacked element", "  rand bit [7:0] u [2] = '{8'h12, 8'h34};\n",
       "u[1]", "8'h34", 0x34},
  });
}

TEST(CheckerInitializedFreeVariable, DISABLED_AGenerateBlockVariableIsHeld) {
  for (const char* open :
       {"  if (1) begin : g\n", "  for (genvar k = 0; k < 1; k++) begin : g\n",
        "  case (1) 1: begin : g\n"}) {
    std::string items = open;
    items += Assumed(kHeldDecl, "a", "16'h1234");
    items += open[2] == 'c' ? "  end endcase\n" : "  end\n";
    SCOPED_TRACE(open);
    EXPECT_EQ(
        FirstAndMoved(Clocked("", items), open[2] == 'f' ? "c.g[0]" : "c.g"),
        (std::vector<uint64_t>{0x1234, 1}));
  }
}

TEST(CheckerInitializedFreeVariable, ANestedCheckersVariableIsHeld) {
  std::string items = "  checker inner(logic clk, sclk);\n";
  items += Assumed(kHeldDecl, "a", "16'h1234");
  items += "  endchecker\n  inner n(clk, sclk);\n";
  EXPECT_EQ(FirstAndMoved(Clocked("", items), "c.n"),
            (std::vector<uint64_t>{0x1234, 1}));
}

}  // namespace
