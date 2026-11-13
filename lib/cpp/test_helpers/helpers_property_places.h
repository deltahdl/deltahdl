#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

struct PlaceCounts {
  size_t passes = 0;
  size_t fails = 0;
  bool operator==(const PlaceCounts&) const = default;
};

inline std::ostream& operator<<(std::ostream& os, const PlaceCounts& counts) {
  return os << counts.passes << " passes, " << counts.fails << " fails";
}

constexpr const char* kPropertyPlaces[] = {
    "module",  "procedural", "generate",        "interface",
    "program", "checker",    "module property", "package property"};

inline std::string PlacedDirective(const std::string& directive,
                                   const std::string& spec) {
  std::string line = "  ";
  line += directive;
  line += " property (";
  line += spec;
  line += ") $display(\"PASS\");";
  if (directive != "cover") line += " else $display(\"FAIL\");";
  line += "\n";
  return line;
}

inline std::string PlacedTop(const std::string& stimulus,
                             const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c, d;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n" +
         stimulus + items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

inline std::string PlacedDeclaration(const std::string& name,
                                     const std::string& declarations,
                                     const std::string& body) {
  return declarations + "  property " + name + "; @(posedge clk) " + body +
         "; endproperty\n";
}

inline std::string PropertyPlaceSource(const std::string& place,
                                       const std::string& directive,
                                       const std::string& body,
                                       const std::string& stimulus,
                                       const std::string& declarations = "") {
  std::string clocked = "@(posedge clk) " + body;
  std::string line = PlacedDirective(directive, clocked);
  if (place == "module") return PlacedTop(stimulus, declarations + line);
  if (place == "procedural") {
    return PlacedTop(stimulus, declarations + "  always @(posedge clk)" +
                                   PlacedDirective(directive, body).substr(1));
  }
  if (place == "generate") {
    return PlacedTop(stimulus,
                     "  if (1) begin : g\n" + declarations + line + "  end\n");
  }
  std::string instance = "  w u(clk, a, b, c, d);\n";
  if (place == "interface" || place == "program") {
    return place + " w(input logic clk, a, b, c, d);\n" + declarations + line +
           "end" + place + "\n" + PlacedTop(stimulus, instance);
  }
  if (place == "checker") {
    return "checker w(clk, a, b, c, d);\n" + declarations + line +
           "endchecker\n" + PlacedTop(stimulus, instance);
  }
  std::string formal = "P(clk, a, b, c, d)";
  if (place == "module property") {
    return PlacedTop(stimulus, PlacedDeclaration("P", declarations, body) +
                                   PlacedDirective(directive, "P"));
  }
  std::string declared = PlacedDeclaration(formal, declarations, body);
  if (place == "package property") {
    return "package pk;\n" + declared + "endpackage\n" +
           PlacedTop(stimulus, PlacedDirective(directive, "pk::" + formal));
  }
  return declared + PlacedTop(stimulus, PlacedDirective(directive, formal));
}

constexpr const char* kDefaultClockedPlaces[] = {
    "default module", "default interface", "default program",
    "default checker"};

inline std::string DefaultClockedSource(const std::string& place,
                                        const std::string& stimulus,
                                        const std::string& items) {
  if (place == "default module") return PlacedTop(stimulus, items);
  std::string unit =
      place == "default checker"
          ? "checker w(clk, a, b, c, d);\n" + items + "endchecker\n"
          : place.substr(8) + " w(input logic clk, a, b, c, d);\n" + items +
                "end" + place.substr(8) + "\n";
  return unit + PlacedTop(stimulus, "  w u(clk, a, b, c, d);\n");
}

inline std::string DeclaredInUnitSource(const std::string& place,
                                        const std::string& directive,
                                        const std::string& body,
                                        const std::string& stimulus,
                                        const std::string& declarations) {
  std::string unit = place.substr(0, place.find(' '));
  std::string header = unit == "checker"
                           ? "checker w(clk, a, b, c, d);\n"
                           : unit + " w(input logic clk, a, b, c, d);\n";
  return header + declarations + "  property P; @(posedge clk) " + body +
         "; endproperty\n" + PlacedDirective(directive, "P") + "end" + unit +
         "\n" + PlacedTop(stimulus, "  w u(clk, a, b, c, d);\n");
}

inline std::string ClockedPlaceSource(const std::string& place,
                                      const std::string& directive,
                                      const std::string& body,
                                      const std::string& stimulus,
                                      const std::string& declarations = "") {
  if (place == "clocked procedural") {
    return PlacedTop(
        stimulus,
        declarations + "  always @(posedge clk)" +
            PlacedDirective(directive, "@(posedge clk) " + body).substr(1));
  }
  if (place.starts_with("default ")) {
    return DefaultClockedSource(
        place, stimulus,
        declarations + "  default clocking cb @(posedge clk); endclocking\n" +
            PlacedDirective(directive, body));
  }
  if (place == "interface property" || place == "checker property") {
    return DeclaredInUnitSource(place, directive, body, stimulus, declarations);
  }
  return PropertyPlaceSource(place, directive, body, stimulus, declarations);
}

inline size_t CountedLines(const std::string& out, const std::string& tag) {
  size_t count = 0;
  std::string line = tag + "\n";
  for (size_t at = out.find(line); at != std::string::npos;
       at = out.find(line, at + 1)) {
    if (at == 0 || out[at - 1] == '\n') ++count;
  }
  return count;
}

inline PlaceCounts CountThroughTheEnd(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  f.ctx.RunFinalBlocks();
  std::cout.rdbuf(old_buf);
  out += captured.str();
  return {CountedLines(out, "PASS"), CountedLines(out, "FAIL")};
}

struct PlacedProperty {
  const char* body;
  PlaceCounts asserted;
  size_t covered;
};

inline void ExpectPropertyCountsInPlace(const std::string& place,
                                        const PlacedProperty& property,
                                        const std::string& stimulus,
                                        const std::string& declarations = "") {
  for (const char* directive : {"assert", "assume"}) {
    SCOPED_TRACE(place + " " + directive + " " + property.body);
    EXPECT_EQ(CountThroughTheEnd(PropertyPlaceSource(
                  place, directive, property.body, stimulus, declarations)),
              property.asserted);
  }
  SCOPED_TRACE(place + " cover " + property.body);
  EXPECT_EQ(CountThroughTheEnd(PropertyPlaceSource(
                place, "cover", property.body, stimulus, declarations)),
            (PlaceCounts{property.covered, 0}));
}

template <typename Places, typename Rows, typename Source>
void ExpectCountsInEachPlace(const Places& places, const Rows& rows,
                             const Source& source) {
  for (const char* name : places) {
    std::string place = name;
    for (const PlacedProperty& row : rows) {
      for (const char* directive : {"assert", "assume"}) {
        SCOPED_TRACE(place + " " + directive + " " + row.body);
        EXPECT_EQ(CountThroughTheEnd(source(place, directive, row.body)),
                  row.asserted);
      }
      SCOPED_TRACE(place + " cover " + row.body);
      EXPECT_EQ(CountThroughTheEnd(source(place, "cover", row.body)),
                (PlaceCounts{row.covered, 0}));
    }
  }
}

inline PlaceCounts SlowClockConsequentCounts(const std::string& consequent) {
  return CountThroughTheEnd(
      "module t;\n"
      "  logic clk = 0, slow = 0;\n"
      "  int tick = 1;\n"
      "  logic a, b;\n"
      "  always #5 clk = ~clk;\n"
      "  always #10 tick = tick + 1;\n"
      "  initial begin #15 slow = 1; #10 slow = 0; #10 slow = 1; end\n"
      "  assign a = tick inside {1, 3};\n"
      "  assign b = tick inside {2, 3};\n"
      "  assert property (@(posedge clk) a |-> @(posedge slow) " +
      consequent +
      ") $display(\"PASS\"); else $display(\"FAIL\");\n"
      "  initial #40 $finish;\n"
      "endmodule\n");
}
