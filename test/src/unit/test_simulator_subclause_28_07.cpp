#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_settle.h"

using namespace delta;

namespace {

TEST(MosSwitchSimulation, NmosConductsDataLowWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(MosSwitchSimulation, NmosConductsDataHighWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, NmosBlocksOutputWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, PmosConductsDataLowWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(MosSwitchSimulation, PmosConductsDataHighWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, PmosBlocksOutputWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, RnmosConductsDataWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, RnmosBlocksOutputWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, RpmosConductsDataWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, RpmosBlocksOutputWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosBlocksOutputWithLowDataAndControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b0;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosPassesUnknownDataWhenConducting) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'bx;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);

  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

TEST(MosSwitchSimulation, NmosPassesHighZDataWhenConducting) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'bz;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosPassesPullDataStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, NmosReducesSupplyDataStrengthToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(MosSwitchSimulation, RnmosReducesStrongDataStrengthToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, PmosPassesPullDataStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, PmosReducesSupplyDataStrengthToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(MosSwitchSimulation, RpmosReducesStrongDataStrengthToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, PmosBlocksOutputWithLowDataAndHighControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b1;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosControlUnknownDoesNotPassDefiniteValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'bx;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

TEST(MosSwitchSimulation, NmosControlHighZDoesNotPassDefiniteValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'bz;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

TEST(MosSwitchSimulation, UnknownControlPassesLAndH) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire n, p;\n"
      "  logic d, c;\n"
      "  nmos g1 (n, d, c);\n"
      "  pmos g2 (p, d, c);\n"
      "  initial begin\n"
      "    d = 0; c = 1'bx;\n"
      "    #1 $display(\"%v %v\", n, p);\n"
      "    d = 1; c = 1'bz;\n"
      "    #1 $display(\"%v %v\", n, p);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "StL StL\n"
            "StH StH\n");
}

TEST(MosSwitchSimulation, ZDataUnderAnUnknownControlDrivesZ) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic d = 1'bz, cx = 1'bx, cz = 1'bz;\n"
      "  wire y1, y2, y3, y4;\n"
      "  nmos (y1, d, cx);\n"
      "  pmos (y2, d, cx);\n"
      "  rnmos (y3, d, cz);\n"
      "  rpmos (y4, d, cz);\n"
      "  initial #1 $display(\"%b %b %b %b\", y1, y2, y3, y4);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z z z z\n");
}

constexpr const char* kMosLevels[] = {"1'b0", "1'b1", "1'bx", "1'bz"};

std::string MosTableShown(const std::string& sw) {
  std::string src = "module t;\n  logic d, c;\n  wire y;\n  ";
  src += sw;
  src += " g(y, d, c);\n  initial begin\n";
  for (const char* data : kMosLevels) {
    for (const char* ctrl : kMosLevels) {
      src += "    d = ";
      src += data;
      src += "; c = ";
      src += ctrl;
      src += "; #1 $write(\"%v \", y);\n";
    }
    src += "    $display;\n";
  }
  src += "  end\nendmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

struct MosTable {
  const char* sw;
  const char* rows;
};

TEST(MosSwitchSimulation, EveryDataAndControlCellOfEachTable) {
  const MosTable kTables[] = {
      {"nmos",
       "HiZ St0 StL StL \nHiZ St1 StH StH \nHiZ StX StX StX \n"
       "HiZ HiZ HiZ HiZ \n"},
      {"pmos",
       "St0 HiZ StL StL \nSt1 HiZ StH StH \nStX HiZ StX StX \n"
       "HiZ HiZ HiZ HiZ \n"},
      {"rnmos",
       "HiZ Pu0 PuL PuL \nHiZ Pu1 PuH PuH \nHiZ PuX PuX PuX \n"
       "HiZ HiZ HiZ HiZ \n"},
      {"rpmos",
       "Pu0 HiZ PuL PuL \nPu1 HiZ PuH PuH \nPuX HiZ PuX PuX \n"
       "HiZ HiZ HiZ HiZ \n"}};
  for (const auto& table : kTables) {
    EXPECT_EQ(MosTableShown(table.sw), table.rows) << table.sw;
  }
}

TEST(MosSwitchSimulation, AConductingSwitchLeavesItsDataInputUndriven) {
  for (const std::string& sw : {"nmos", "pmos", "rnmos", "rpmos"}) {
    const bool kActiveLow = sw == "pmos" || sw == "rpmos";
    std::string src = "module t;\n  wire d, y;\n  logic c = ";
    src += kActiveLow ? "1'b0" : "1'b1";
    src += ";\n  ";
    src += sw;
    src +=
        " g(y, d, c);\n"
        "  assign y = 1'b1;\n"
        "  initial #1 $display(\"%b %b\", d, y);\n"
        "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "z 1\n") << sw;
  }
}

struct MosGenerateForm {
  const char* open;
  const char* close;
};

TEST(MosSwitchSimulation, ASwitchInAGenerateBlockDrivesItsTable) {
  const MosGenerateForm kForms[] = {
      {"  for (genvar k = 0; k < 1; k++) begin : g\n", "  end\n"},
      {"  for (genvar k = 0; k < 1; k++) begin\n", "  end\n"},
      {"  if (1) begin : c1\n", "  end\n"},
      {"  if (1) begin\n", "  end\n"},
      {"  case (1)\n    1: begin : c2\n", "    end\n  endcase\n"},
      {"  case (1)\n    1: begin\n", "    end\n  endcase\n"}};
  for (const auto& form : kForms) {
    std::string src = "module t;\n  logic d, c;\n  wire [3:0] y;\n";
    src += form.open;
    src +=
        "    nmos g0(y[0], d, c);\n"
        "    pmos g1(y[1], d, c);\n"
        "    rnmos g2(y[2], d, c);\n"
        "    rpmos g3(y[3], d, c);\n";
    src += form.close;
    src +=
        "  initial begin\n"
        "    d = 1'b1; c = 1'b0; #1 $write(\"%b \", y);\n"
        "    d = 1'b0; c = 1'b1; #1 $display(\"%b\", y);\n"
        "  end\n"
        "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "1z1z z0z0\n") << form.open;
  }
}

std::string MosTransitionsShown(const std::string& sw, const std::string& delay,
                                bool start_high) {
  const bool kActiveLow = sw == "pmos" || sw == "rpmos";
  const char* on = kActiveLow ? "1'b0" : "1'b1";
  const char* off = kActiveLow ? "1'b1" : "1'b0";
  const char* first = start_high ? "1'b1" : "1'b0";
  const char* second = start_high ? "1'b0" : "1'b1";
  std::string src = "module t;\n  logic d, c;\n  wire y;\n  ";
  src += sw;
  src += " ";
  src += delay;
  src +=
      " g(y, d, c);\n"
      "  always @(y) $display(\"%0t %v\", $time, y);\n"
      "  initial begin\n    d = ";
  src += first;
  src += "; c = ";
  src += on;
  src += ";\n    #20 d = ";
  src += second;
  src += ";\n    #20 c = ";
  src += off;
  src += ";\n    #20 c = ";
  src += on;
  src += ";\n    #20 d = 1'bx;\n    #20 d = ";
  src += first;
  src +=
      ";\n"
      "    #20 c = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

std::string Strengthened(const std::string& times, const std::string& prefix) {
  std::string out;
  for (char ch : times) {
    if (ch == '@') {
      out += prefix;
    } else {
      out += ch;
    }
  }
  return out;
}

struct MosTiming {
  const char* delay;
  const char* low_first;
  const char* high_first;
};

TEST(MosSwitchSimulation, DelaysTimeEachTransitionOfEverySwitch) {
  const MosTiming kCases[] = {
      {"#(6, 4, 8)", "4 @0\n26 @1\n48 HiZ\n66 @1\n84 @X\n104 @0\n124 @L\n",
       "6 @1\n24 @0\n48 HiZ\n64 @0\n84 @X\n106 @1\n124 @H\n"},
      {"#(8, 6, 3)", "6 @0\n28 @1\n43 HiZ\n68 @1\n83 @X\n106 @0\n123 @L\n",
       "8 @1\n26 @0\n43 HiZ\n66 @0\n83 @X\n108 @1\n123 @H\n"},
      {"#(6, 4)", "4 @0\n26 @1\n44 HiZ\n66 @1\n84 @X\n104 @0\n124 @L\n",
       "6 @1\n24 @0\n44 HiZ\n64 @0\n84 @X\n106 @1\n124 @H\n"},
      {"#(4, 6)", "6 @0\n24 @1\n44 HiZ\n64 @1\n84 @X\n106 @0\n124 @L\n",
       "4 @1\n26 @0\n44 HiZ\n66 @0\n84 @X\n104 @1\n124 @H\n"},
      {"#5", "5 @0\n25 @1\n45 HiZ\n65 @1\n85 @X\n105 @0\n125 @L\n",
       "5 @1\n25 @0\n45 HiZ\n65 @0\n85 @X\n105 @1\n125 @H\n"},
      {"", "0 @0\n20 @1\n40 HiZ\n60 @1\n80 @X\n100 @0\n120 @L\n",
       "0 @1\n20 @0\n40 HiZ\n60 @0\n80 @X\n100 @1\n120 @H\n"}};
  for (const std::string& sw : {"nmos", "pmos", "rnmos", "rpmos"}) {
    const std::string kPrefix = sw[0] == 'r' ? "Pu" : "St";
    for (const auto& timing : kCases) {
      EXPECT_EQ(MosTransitionsShown(sw, timing.delay, false),
                Strengthened(timing.low_first, kPrefix))
          << sw << " " << timing.delay;
      EXPECT_EQ(MosTransitionsShown(sw, timing.delay, true),
                Strengthened(timing.high_first, kPrefix))
          << sw << " " << timing.delay;
    }
  }
}

}  // namespace
