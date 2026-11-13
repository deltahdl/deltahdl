#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

std::string AttemptBench(const std::string& items, const std::string& drive,
                         const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, c = 0;\n"
         "  int data = 0, do1 = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  " +
         items +
         "\n"
         "  initial begin\n" +
         drive +
         "    #40 $finish;\n"
         "  end\n"
         "endmodule\n";
}

const char kOverlap[] =
    "    #10 c = 1; data = 5;\n"
    "    #10 data = 6;\n"
    "    #10 c = 0; do1 = 5;\n"
    "    #10 do1 = 6;\n"
    "    #10 do1 = 0;\n";

const char kOnce[] =
    "    #10 c = 1; data = 21;\n"
    "    #10 c = 0; data = 0; do1 = 5;\n"
    "    #10 do1 = 0;\n";

const char kHit[] = "$display(\"hit %0t\", $time);";

std::string Covered(const std::string& sequence) {
  return "cover property (@(posedge clk) " + sequence + ") " + kHit;
}

const char kInputSub[] =
    "sequence sub(untyped d, local input int lv); 1 ##2 (d == lv); "
    "endsequence\n  ";

TEST(LocalFormalAttemptCopy, EachAttemptKeepsItsInputFormal) {
  ExpectLines(
      AttemptBench(kInputSub + Covered("c ##0 sub(do1, data)"), kOverlap),
      "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, EachAttemptKeepsAnInferredInputFormal) {
  ExpectLines(
      AttemptBench("sequence sub(untyped d, local int lv); 1 ##2 (d == lv); "
                   "endsequence\n  " +
                       Covered("c ##0 sub(do1, data)"),
                   kOverlap),
      "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, EachAttemptEvaluatesTheDefaultAtItsStart) {
  ExpectLines(AttemptBench("sequence sub(untyped d, local input int lv = "
                           "data); 1 ##2 (d == lv); endsequence\n  " +
                               Covered("c ##0 sub(do1)"),
                           kOverlap),
              "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, AnInoutUpdateStaysInItsAttempt) {
  ExpectLines(
      AttemptBench("sequence sub(untyped d, local inout int lv);\n"
                   "    (1, lv += 1) ##2 (d == lv);\n"
                   "  endsequence\n"
                   "  sequence r; int v; (c, v = data) ##0 sub(do1, v); "
                   "endsequence\n  " +
                       Covered("r"),
                   "    #10 c = 1; data = 5;\n"
                   "    #10 data = 6;\n"
                   "    #10 c = 0; do1 = 6;\n"
                   "    #10 do1 = 7;\n"
                   "    #10 do1 = 0;\n"),
      "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, EachAttemptAssignsItsOwnOutputBack) {
  ExpectLines(AttemptBench("sequence sub(local output int lv);\n"
                           "    (1, lv = data) ##2 1;\n"
                           "  endsequence\n"
                           "  sequence r; int v; c ##0 sub(v) ##0 (do1 == v); "
                           "endsequence\n  " +
                               Covered("r"),
                           kOverlap),
              "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, EachInnerAttemptOfOneOuterAttemptStartsAnew) {
  ExpectLines(
      AttemptBench(
          "sequence sub(untyped d, local input int lv); 1 ##1 (d == "
          "lv); endsequence\n"
          "  cover sequence (@(posedge clk) c ##[1:2] sub(do1, data)) " +
              std::string(kHit),
          "    #10 c = 1;\n"
          "    #10 c = 0; data = 5;\n"
          "    #10 data = 6; do1 = 5;\n"
          "    #10 do1 = 6;\n"
          "    #10 do1 = 0;\n"),
      "hit ", "35 45");
}

TEST(LocalFormalAttemptCopy, EachRepetitionOfAnInstanceStartsAnew) {
  ExpectLines(
      AttemptBench("sequence sub(untyped d, local input int lv); (d == lv); "
                   "endsequence\n  " +
                       Covered("c ##0 sub(do1, data) [*2]"),
                   "    #10 c = 1; data = 5; do1 = 5;\n"
                   "    #10 c = 0; data = 6; do1 = 6;\n"
                   "    #10 data = 0; do1 = 1;\n"),
      "hit ", "25");
}

TEST(LocalFormalAttemptCopy, AnAssertedImplicationKeepsEachAttemptsCopy) {
  const std::string kSrc = AttemptBench(
      kInputSub +
          std::string("assert property (@(posedge clk) c |-> sub(do1, data))\n"
                      "    else $display(\"fail %0t\", $time);\n  ") +
          Covered("c ##0 sub(do1, data)"),
      kOverlap);
  ExpectLines(kSrc, "fail ", "");
  ExpectLines(kSrc, "hit ", "35 45");
}

struct PlacedBench {
  std::string place;
  std::string outside;
  std::string items;
};

const char kCoverSub[] =
    "cover property (@(posedge clk) c ##0 @sub(do1, data)) $display(\"hit "
    "%0t\", $time);";

std::string Scoped(const std::string& use, const std::string& prefix) {
  std::string out = use;
  for (std::size_t at = out.find('@'); at != std::string::npos;
       at = out.find('@', at + prefix.size())) {
    if (out.compare(at, 2, "@(") == 0) {
      ++at;
      continue;
    }
    out.replace(at, 1, prefix);
  }
  return out;
}

std::vector<PlacedBench> AttemptPlaces(const std::string& sub,
                                       const std::string& use = kCoverSub) {
  const std::string kHere = Scoped(use, "");
  const std::string kPorts =
      "(input logic clk, c, input var int data, do1);\n  " + sub + "\n  " +
      kHere + "\n";
  std::vector<PlacedBench> out;
  out.push_back({"module", "", sub + "\n  " + kHere});
  out.push_back(
      {"interface",
       "interface ifc(input logic clk);\n  " + sub + "\nendinterface\n",
       "ifc i(clk);\n  " + Scoped(use, "i.")});
  out.push_back({"program", "program pg" + kPorts + "endprogram\n",
                 "pg p(clk, c, data, do1);"});
  out.push_back({"checker",
                 "checker ck(logic clk, logic c, int data, int do1);\n  " +
                     sub + "\n  " + kHere + "\nendchecker\n",
                 "ck k(clk, c, data, do1);"});
  out.push_back({"clocking block", "",
                 "clocking cb @(posedge clk);\n    " + sub +
                     "\n  endclocking\n  " + Scoped(use, "cb.")});
  out.push_back({"package by name", "package pk;\n  " + sub + "\nendpackage\n",
                 Scoped(use, "pk::")});
  out.push_back({"package by import",
                 "package pk;\n  " + sub + "\nendpackage\n",
                 "import pk::*;\n  " + kHere});
  out.push_back({"compilation unit", sub + "\n", kHere});
  out.push_back(
      {"generate", "",
       "if (1) begin : g\n    " + sub + "\n    " + kHere + "\n  end"});
  return out;
}

TEST(LocalFormalAttemptCopy, EveryPlaceKeepsEachAttemptsCopy) {
  for (const auto& placed : AttemptPlaces(kInputSub)) {
    if (placed.place == "compilation unit") continue;
    ExpectLines(AttemptBench(placed.items, kOverlap, placed.outside), "hit ",
                "35 45");
  }
}

TEST(LocalFormalAttemptCopy,
     DISABLED_ACompilationUnitSequenceKeepsEachAttemptsCopy) {
  for (const auto& placed : AttemptPlaces(kInputSub)) {
    if (placed.place != "compilation unit") continue;
    ExpectLines(AttemptBench(placed.items, kOverlap, placed.outside), "hit ",
                "35 45");
  }
}

TEST(LocalFormalInitialValue, AnInoutFromAnotherTypeIsCast) {
  ExpectLines(
      AttemptBench("sequence sub(untyped d, local inout logic [3:0] lv); 1 ##1 "
                   "(d == lv); endsequence\n"
                   "  sequence r; int v; (c, v = data) ##0 sub(do1, v); "
                   "endsequence\n  " +
                       Covered("r"),
                   kOnce),
      "hit ", "25");
}

TEST(LocalFormalInitialValue, ADefaultIsCastToTheFormal) {
  ExpectLines(AttemptBench("sequence sub(untyped d, local input logic [3:0] "
                           "lv = data); 1 ##1 (d == lv); endsequence\n  " +
                               Covered("c ##0 sub(do1)"),
                           kOnce),
              "hit ", "25");
}

TEST(LocalFormalInitialValue, APropertyInputIsCast) {
  const std::string kSrc = AttemptBench(
      "property pin(local input logic [3:0] lv); 1 ##1 (do1 == lv); "
      "endproperty\n"
      "  assert property (@(posedge clk) c |-> pin(data))\n"
      "    else $display(\"fail %0t\", $time);",
      kOnce);
  ExpectLines(kSrc, "fail ", "");
}

TEST(LocalFormalInitialValue, AnUnpackedOrWiderActualIsCast) {
  ExpectLines(AttemptBench("byte b4 [4] = '{0, 0, 1, 2};\n"
                           "  longint wide = 64'h100000102;\n"
                           "  sequence sub(untyped d, local input int lv); 1 "
                           "##1 (d == lv); endsequence\n  " +
                               Covered("c ##0 sub(do1, b4)") + "\n  " +
                               Covered("c ##0 sub(do1, wide)"),
                           "    #10 c = 1;\n"
                           "    #10 c = 0; do1 = 258;\n"
                           "    #10 do1 = 0;\n"),
              "hit ", "25 25");
}

const char* const kBodyLocalReads[] = {
    ("sequence sub(untyped d, local input int lv); int g = lv; 1 ##1 (d == g); "
     "endsequence\n  cover property (@(posedge clk) c ##0 sub(do1, data)) "),
    ("sequence sub(untyped d, local input logic [3:0] lv); int g = lv; 1 ##1 "
     "(d == g); endsequence\n  cover property (@(posedge clk) c ##0 sub(do1, "
     "data)) "),
    ("sequence sub(untyped d, local input logic [3:0] lv = data); int g = lv; "
     "1 ##1 (d == g); endsequence\n  cover property (@(posedge clk) c ##0 "
     "sub(do1)) "),
    ("sequence sub(untyped d, local inout logic [3:0] lv); int g = lv; 1 ##1 "
     "(d == g); endsequence\n  sequence r; int v; (c, v = data) ##0 sub(do1, "
     "v); endsequence\n  cover property (@(posedge clk) r) ")};

TEST(LocalFormalInitialValue, DISABLED_ABodyLocalReadsTheFormalsValue) {
  for (const char* items : kBodyLocalReads) {
    ExpectLines(AttemptBench(items + std::string(kHit), kOnce), "hit ", "25");
  }
}

TEST(LocalFormalInitialValue, DISABLED_APropertyBodyLocalReadsTheFormal) {
  ExpectLines(
      AttemptBench("property pin(local input logic [3:0] lv); int g = "
                   "lv; 1 ##1 (do1 == g); endproperty\n"
                   "  assert property (@(posedge clk) c |-> pin(data))\n"
                   "    else $display(\"fail %0t\", $time);",
                   kOnce),
      "fail ", "");
}

TEST(LocalFormalInitialValue, DISABLED_ALaterBodyLocalReadsAnEarlierOne) {
  ExpectLines(AttemptBench("sequence sub(local input logic x, y); logic g = x, "
                           "h = g || y; 1 ##1 (g && h); endsequence\n  " +
                               Covered("c ##0 sub(1'b1, 1'b0)"),
                           kOnce),
              "hit ", "25");
}

TEST(LocalFormalInitialValue, DISABLED_EveryPlaceGivesABodyLocalTheFormal) {
  for (const auto& placed : AttemptPlaces(
           "sequence sub(untyped d, local input int lv); int g = lv; 1 ##2 "
           "(d == g); endsequence")) {
    ExpectLines(AttemptBench(placed.items, kOverlap, placed.outside), "hit ",
                "35 45");
  }
}

std::string WriteBackBench(const std::string& actual_decl,
                           const std::string& check) {
  return AttemptBench(
      "sequence sub(local output int lv); (1, lv = data) ##1 "
      "1; endsequence\n  sequence r; " +
          actual_decl + "; c ##0 sub(v) ##0 " + check + "; endsequence\n  " +
          Covered("r"),
      kOnce);
}

TEST(LocalFormalWriteBack, AnOutputIsCastToItsActualsType) {
  ExpectLines(WriteBackBench("logic [3:0] v", "(v == 5)"), "hit ", "25");
  ExpectLines(WriteBackBench("logic [3:0] v", "(v == 21)"), "hit ", "");
}

TEST(LocalFormalWriteBack, DISABLED_AnOutputIsConvertedToARealActual) {
  ExpectLines(WriteBackBench("real v", "(v == 21.0)"), "hit ", "25");
}

TEST(LocalFormalWriteBack, DISABLED_EachMatchingThreadAssignsItsOwnCopy) {
  ExpectLines(AttemptBench("sequence sub(local output int lv); (1, lv = 1) or "
                           "(1, lv = 2); endsequence\n"
                           "  sequence r1; int v; c ##0 sub(v) ##1 (v == 1); "
                           "endsequence\n"
                           "  sequence r2; int v; c ##0 sub(v) ##1 (v == 2); "
                           "endsequence\n  " +
                               Covered("r1") + "\n  " + Covered("r2"),
                           kOnce),
              "hit ", "25 25");
}

const char kOutputSub[] =
    "sequence sub(untyped d, local output int lv); (1, lv = d) ##2 1; "
    "endsequence";

const char kWriteBackUse[] =
    "sequence r; int v; c ##0 @sub(data, v) ##0 (do1 == v); endsequence\n"
    "  cover property (@(posedge clk) r) $display(\"hit %0t\", $time);";

TEST(LocalFormalWriteBack, AModuleSequenceWritesBackPerAttempt) {
  for (const auto& placed : AttemptPlaces(kOutputSub, kWriteBackUse)) {
    if (placed.place == "module") {
      ExpectLines(AttemptBench(placed.items, kOverlap, placed.outside), "hit ",
                  "35 45");
    }
  }
}

TEST(LocalFormalWriteBack, DISABLED_EveryOtherPlaceWritesBackPerAttempt) {
  for (const auto& placed : AttemptPlaces(kOutputSub, kWriteBackUse)) {
    if (placed.place != "module") {
      ExpectLines(AttemptBench(placed.items, kOverlap, placed.outside), "hit ",
                  "35 45");
    }
  }
}

std::string PropertyWriteBack(const std::string& check) {
  return AttemptBench(std::string(kOutputSub) +
                          "\n  property p; int v; c ##0 sub(data, v) |-> " +
                          check +
                          "; endproperty\n"
                          "  assert property (@(posedge clk) p) else "
                          "$display(\"fail %0t\", $time);",
                      kOverlap);
}

TEST(LocalFormalWriteBack, AnInstanceInAPropertyWritesBack) {
  ExpectLines(PropertyWriteBack("(do1 == v)"), "fail ", "");
  ExpectLines(PropertyWriteBack("(do1 != v)"), "fail ", "35 45");
}

TEST(LocalFormalInitialValue, DISABLED_ARealInputHoldsItsActual) {
  ExpectLines(AttemptBench("sequence sr(local input real r); 1 ##1 (r > 20.5 "
                           "&& r < 21.5); endsequence\n  " +
                               Covered("c ##0 sr(data)"),
                           kOnce),
              "hit ", "25");
}

}  // namespace
