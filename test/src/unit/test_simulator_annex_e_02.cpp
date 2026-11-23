#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

constexpr const char* kHeldThenLost = "A 1\nB x\nC x\n";
constexpr const char* kHeldForever = "A 1\nB 1\nC 1\n";
constexpr const char* kLostAtOnce = "A x\nB x\nC x\n";

std::string Readings(const std::string& above, const std::string& decl) {
  SimFixture f;
  std::string out =
      PreprocessAndCapture(above +
                               "\nmodule t;\n"
                               "  reg en, d;\n"
                               "  " +
                               decl +
                               "\n"
                               "  bufif1 (cap, d, en);\n"
                               "  initial begin\n"
                               "    en = 1; d = 1;\n"
                               "    #1 en = 0;\n"
                               "    #5 $display(\"A %b\", cap);\n"
                               "    #10 $display(\"B %b\", cap);\n"
                               "    #1000 $display(\"C %b\", cap);\n"
                               "  end\n"
                               "endmodule\n",
                           f);
  EXPECT_FALSE(f.diag.HasErrors()) << decl;
  return out;
}

TEST(DefaultDecayTimeSim, ATriregWithNoDecayTimeOfItsOwnLosesItsChargeAfterIt) {
  EXPECT_EQ(Readings("`default_decay_time 10", "trireg cap;"), kHeldThenLost);
  EXPECT_EQ(Readings("`default_decay_time 1_000", "trireg cap;"),
            "A 1\nB 1\nC x\n");
}

TEST(DefaultDecayTimeSim, InfiniteKeepsTheChargeOfATriregWithNoDecayTime) {
  EXPECT_EQ(Readings("`default_decay_time infinite", "trireg cap;"),
            kHeldForever);
  EXPECT_EQ(Readings("`default_decay_time 10\n`default_decay_time infinite",
                     "trireg cap;"),
            kHeldForever);
}

TEST(DefaultDecayTimeSim, InfiniteLeavesATriregWithItsOwnDecayTimeDecaying) {
  EXPECT_EQ(
      Readings("`default_decay_time infinite", "trireg #(0, 0, 100) cap;"),
      "A 1\nB 1\nC x\n");
}

TEST(DefaultDecayTimeSim, AZeroArgumentLosesTheChargeAtOnce) {
  EXPECT_EQ(Readings("`default_decay_time 0", "trireg cap;"), kLostAtOnce);
}

TEST(DefaultDecayTimeSim, AnyThirdDelayOfTheTriregsOwnIsKept) {
  for (const char* decl : {"trireg #(0, 0, 40:50:60) cap;",
                           "parameter P = 50;\n  trireg #(0, 0, P) cap;"}) {
    EXPECT_EQ(Readings("`default_decay_time 10", decl), "A 1\nB 1\nC x\n")
        << decl;
  }
  EXPECT_EQ(Readings("`default_decay_time 10", "trireg #(0, 0, 0) cap;"),
            kLostAtOnce);
}

TEST(DefaultDecayTimeSim, ATriregWithNoThirdDelayTakesTheDefault) {
  for (const char* decl :
       {"trireg #(0, 0) cap;", "trireg #0 cap;", "trireg (large) cap;",
        "trireg (small) cap;", "trireg cap, other;", "trireg other, cap;"}) {
    EXPECT_EQ(Readings("`default_decay_time 10", decl), kHeldThenLost) << decl;
  }
}

TEST(DefaultDecayTimeSim, EveryBitOfAVectorTriregTakesTheDefault) {
  SimFixture f;
  std::string out = PreprocessAndCapture(
      "`default_decay_time 10\n"
      "module t;\n"
      "  reg en;\n"
      "  reg [1:0] d;\n"
      "  trireg [1:0] cap;\n"
      "  assign cap = en ? d : 2'bzz;\n"
      "  initial begin\n"
      "    en = 1; d = 2'b10;\n"
      "    #1 en = 0;\n"
      "    #5 $display(\"A %b\", cap);\n"
      "    #10 $display(\"B %b\", cap);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "A 10\nB xx\n");
}

TEST(DefaultDecayTimeSim, ATriregBelowTheTopTakesTheDefault) {
  for (const char* where : {"module c(input en, input d, output r);\n"
                            "  trireg cap;\n"
                            "  bufif1 (cap, d, en);\n"
                            "  assign r = cap;\n"
                            "endmodule\n"
                            "module t;\n"
                            "  reg en, d;\n"
                            "  wire cap;\n"
                            "  c u(en, d, cap);\n",
                            "module t;\n"
                            "  reg en, d;\n"
                            "  wire cap;\n"
                            "  if (1) begin : g\n"
                            "    trireg n;\n"
                            "    bufif1 (n, d, en);\n"
                            "    assign cap = n;\n"
                            "  end\n"}) {
    SimFixture f;
    std::string out =
        PreprocessAndCapture(std::string("`default_decay_time 10\n") + where +
                                 "  initial begin\n"
                                 "    en = 1; d = 1;\n"
                                 "    #1 en = 0;\n"
                                 "    #5 $display(\"A %b\", cap);\n"
                                 "    #10 $display(\"B %b\", cap);\n"
                                 "  end\n"
                                 "endmodule\n",
                             f);
    EXPECT_FALSE(f.diag.HasErrors()) << where;
    EXPECT_EQ(out, "A 1\nB x\n") << where;
  }
}

}  // namespace
