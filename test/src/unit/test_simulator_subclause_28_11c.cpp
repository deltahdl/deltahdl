#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string StrengthShown(const std::string& body) {
  std::string src = "module t;\n  reg a;\n  wire w;\n  ";
  src += body;
  src +=
      "\n  initial begin\n"
      "    a = 0;\n"
      "    #1 $display(\"%v\", w);\n"
      "    a = 1;\n"
      "    #1 $display(\"%v\", w);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

struct StrengthRun {
  const char* body;
  const char* shown;
};

TEST(StrengthScaleOccupancy, AZValueHasStrengthOnlyAtTheHighImpedanceLevel) {
  const StrengthRun kCases[] = {
      {"assign w = 1'bz;", "HiZ\nHiZ\n"},
      {"assign (strong0, strong1) w = a ? 1'bz : 1'bz;", "HiZ\nHiZ\n"},
      {"assign (highz0, strong1) w = 0;", "HiZ\nHiZ\n"},
      {"assign (strong0, highz1) w = 1;", "HiZ\nHiZ\n"},
      {"assign (highz0, strong1) w = a;", "HiZ\nSt1\n"},
      {"buf (strong0, highz1) b(w, a);", "St0\nHiZ\n"},
      {"buf (highz0, strong1) b(w, a);", "HiZ\nSt1\n"},
      {"bufif1 (strong0, strong1) b(w, a, 1'b0);", "HiZ\nHiZ\n"}};
  for (const auto& c : kCases) {
    EXPECT_EQ(StrengthShown(c.body), c.shown) << c.body;
  }
}

TEST(StrengthScaleOccupancy, AKnownValueHasOnePartAndAnUnknownBoth) {
  const StrengthRun kCases[] = {
      {"assign (pull0, weak1) w = a;", "Pu0\nWe1\n"},
      {"assign (strong0, strong1) w = a ? 1'bx : 1'bx;", "StX\nStX\n"},
      {"assign (pull0, pull1) w = a;\n  assign (pull0, pull1) w = ~a;",
       "PuX\nPuX\n"}};
  for (const auto& c : kCases) {
    EXPECT_EQ(StrengthShown(c.body), c.shown) << c.body;
  }
}

TEST(DrivingStrengthPropagation, AGateOutputAloneCarriesItsDrivingStrength) {
  const StrengthRun kCases[] = {
      {"buf (pull0, weak1) b(w, a);", "Pu0\nWe1\n"},
      {"not (weak0, supply1) n(w, a);", "Su1\nWe0\n"},
      {"and (strong0, pull1) g(w, a, 1'b1);", "St0\nPu1\n"},
      {"or (supply0, weak1) g(w, a, 1'b0);", "Su0\nWe1\n"},
      {"xor (weak0, weak1) g(w, a, 1'b0);", "We0\nWe1\n"},
      {"bufif1 (pull0, strong1) b(w, a, 1'b1);", "Pu0\nSt1\n"},
      {"notif0 (supply0, pull1) n(w, a, 1'b0);", "Pu1\nSu0\n"},
      {"buf b(w, a);", "St0\nSt1\n"},
      {"if (1) begin : gb\n    buf (weak0, pull1) b(w, a);\n  end",
       "We0\nPu1\n"}};
  for (const auto& c : kCases) {
    EXPECT_EQ(StrengthShown(c.body), c.shown) << c.body;
  }
}

TEST(DrivingStrengthPropagation,
     AContinuousAssignmentCarriesItsDrivingStrength) {
  const StrengthRun kCases[] = {
      {"assign (weak0, pull1) w = a;", "We0\nPu1\n"},
      {"assign (supply0, strong1) w = a;", "Su0\nSt1\n"},
      {"assign w = a;", "St0\nSt1\n"}};
  for (const auto& c : kCases) {
    EXPECT_EQ(StrengthShown(c.body), c.shown) << c.body;
  }
}

}  // namespace
