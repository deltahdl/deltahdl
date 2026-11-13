#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kSavedSignals =
    "  logic clk = 0;\n"
    "  logic [3:0] v = 4'b1010;\n"
    "  always #5 clk = ~clk;\n"
    "  initial #8 $finish;\n";

std::string SavedPlaceSource(const std::string& place,
                             const std::string& body) {
  std::string procedure = "always @(posedge clk) begin\n";
  if (place == "program") procedure = "initial begin @(posedge clk);\n";
  if (place == "checker") procedure = "always_ff @(posedge clk) begin\n";
  std::string items = "  int i, s;\n  " + procedure + body + "  end\n";
  if (place == "module") {
    return "module t;\n" + std::string(kSavedSignals) + items + "endmodule\n";
  }
  if (place == "generate") {
    return "module t;\n" + std::string(kSavedSignals) + "  if (1) begin : g\n" +
           items + "  end\nendmodule\n";
  }
  std::string header =
      place == "checker"
          ? "checker w(clk, logic [3:0] v);\n"
          : place + " w(input logic clk, input logic [3:0] v);\n";
  return header + items + "end" + place + "\nmodule t;\n" + kSavedSignals +
         "  w u(clk, v);\nendmodule\n";
}

std::string SortedOutput(const std::string& text) {
  std::vector<std::string> lines;
  size_t at = 0;
  while (at < text.size()) {
    size_t end = text.find('\n', at);
    std::string line = text.substr(at, end - at);
    if (!line.starts_with("$finish") && !line.starts_with("cover ")) {
      lines.push_back(line);
    }
    at = end + 1;
  }
  std::sort(lines.begin(), lines.end());
  std::string out;
  for (const std::string& line : lines) out.append(line).append("\n");
  return out;
}

std::string Verdicts(const std::string& directive, const std::string& expr,
                     const std::string& shown) {
  std::string pass = "$display(\"p %0d\", " + shown + ");";
  if (directive.starts_with("cover")) {
    return directive + " (" + expr + ") " + pass;
  }
  return directive + " (" + expr + ") " + pass + " else $display(\"f %0d\", " +
         shown + ");";
}

constexpr const char* kSavedDirectives[] = {
    "assert property", "assume property", "cover property", "cover sequence"};

constexpr const char* kSavedPlaces[] = {"module", "generate", "interface",
                                        "program", "checker"};

struct SavedRow {
  const char* body;
  const char* expr;
  const char* shown;
  const char* tail;
};

constexpr SavedRow kSavedRows[] = {
    {"    for (int j = 0; j < 4; j++) ", "v[j]", "j", ""},
    {"    for (i = 0; i < 4; i++) ", "v[const'(i)]", "const'(i)", ""},
    {"    begin automatic int k = 1; ", "v[k]", "k", " k = 0; end"},
    {"    begin automatic int k = 2; ", "v[k]", "k", " k = 1; end"}};

std::string Expected(const std::string& directive, const SavedRow& row) {
  bool cover = directive.starts_with("cover");
  std::string body = row.body;
  if (body.find("for") != std::string::npos) {
    return cover ? "p 1\np 3\n" : "f 0\nf 2\np 1\np 3\n";
  }
  if (body.find("= 1;") != std::string::npos) return "p 1\n";
  return cover ? "" : "f 2\n";
}

std::string SavedBody(const std::string& place, const std::string& directive,
                      const SavedRow& row) {
  std::string head = row.body;
  std::string tail = row.tail;
  if (place == "checker") {
    size_t at = head.find("for (i = 0");
    if (at != std::string::npos) head.replace(at, 10, "for (int i = 0");
    tail = tail.empty() ? "" : " end";
  }
  return head + Verdicts(directive, row.expr, row.shown) + tail + "\n";
}

TEST(
    ProceduralAssertionArgumentsRun,
    EachSavedValueIsReadInTheAssertionAndItsActionBlockForEachKindInEachPlace) {
  for (const char* place : kSavedPlaces) {
    for (const char* directive : kSavedDirectives) {
      for (const SavedRow& row : kSavedRows) {
        std::string src =
            SavedPlaceSource(place, SavedBody(place, directive, row));
        SCOPED_TRACE(src);
        SimFixture f;
        EXPECT_EQ(SortedOutput(RunCapture(src, f)), Expected(directive, row));
      }
    }
  }
}

TEST(ProceduralAssertionArgumentsRun,
     ATemporalAssertionsActionBlockReadsItsSavedValuesAtItsVerdict) {
  for (const char* directive : kSavedDirectives) {
    std::string body = std::string("    for (int j = 0; j < 4; j++) ") +
                       Verdicts(directive, "v[j] ##1 v[j]", "j * 100 + $time") +
                       "\n";
    std::string src = SavedPlaceSource("module", body);
    src.replace(src.find("#8 $finish"), 10, "#18 $finish");
    SCOPED_TRACE(src);
    SimFixture f;
    bool cover = std::string(directive).starts_with("cover");
    EXPECT_EQ(
        SortedOutput(RunCapture(src, f)),
        cover ? "p 115\np 315\n" : "f 15\nf 205\nf 215\nf 5\np 115\np 315\n");
  }
}

constexpr const char* kStaticWrites[] = {
    "assert property (v[const'(s)]) begin s = 7; z = 9; end",
    "assert property (!v[const'(s)]) else begin s = 7; z = 9; end",
    "assume property (v[const'(s)]) begin s = 7; z = 9; end",
    "assume property (!v[const'(s)]) else begin s = 7; z = 9; end",
    "cover property (v[const'(s)]) begin s = 7; z = 9; end",
    "cover sequence (v[const'(s)]) begin s = 7; z = 9; end"};

TEST(ProceduralAssertionArgumentsRun,
     AnActionBlocksWriteOfAStaticVariableTakesEffectForEachKind) {
  for (const char* statement : kStaticWrites) {
    std::string src = std::string(
                          "module t;\n"
                          "  logic clk = 0;\n"
                          "  logic [3:0] v = 4'b1010;\n"
                          "  int s = 1, z = 0;\n"
                          "  always #5 clk = ~clk;\n"
                          "  always @(posedge clk) ") +
                      statement +
                      "\n"
                      "  initial #8 $display(\"%0d %0d\", s, z);\n"
                      "  initial #9 $finish;\n"
                      "endmodule\n";
    SCOPED_TRACE(src);
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "7 9\n$finish at time 9\n");
  }
}

}  // namespace
