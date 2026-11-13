#include <gtest/gtest.h>

#include <cstddef>
#include <ostream>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kDistSignals =
    "  logic clk = 0;\n"
    "  int v = 1;\n"
    "  real r = 0.5;\n"
    "  always #5 clk = ~clk;\n"
    "  always @(negedge clk) begin v++; r = v * 0.5; end\n"
    "  initial #60 $finish;\n";

constexpr const char* kDistDeclarations =
    "  sequence s1; v dist {2 := 1, 3 := 1}; endsequence\n"
    "  sequence s1i; v inside {2, 3}; endsequence\n"
    "  property p1; @(posedge clk) v dist {4 := 1}; endproperty\n"
    "  property p1i; @(posedge clk) v inside {4}; endproperty\n";

size_t Count(std::string_view out, std::string_view line) {
  size_t n = 0;
  for (size_t at = out.find(line); at != std::string_view::npos;
       at = out.find(line, at + 1)) {
    ++n;
  }
  return n;
}

struct Counts {
  size_t passes;
  size_t fails;
  bool operator==(const Counts&) const = default;
};

std::ostream& operator<<(std::ostream& os, const Counts& counts) {
  return os << counts.passes << " passes and " << counts.fails << " fails";
}

std::string Statement(const std::string& directive, const std::string& spec,
                      const std::string& tag) {
  std::string out =
      directive + " (" + spec + ") $display(\"" + tag + " pass\");";
  if (directive.starts_with("cover")) return out;
  return out + " else $display(\"" + tag + " fail\");";
}

struct DistRow {
  const char* directive;
  const char* dist_spec;
  const char* inside_spec;
  Counts counts;
};

void ExpectDistReadAsInside(const DistRow& row) {
  SCOPED_TRACE(std::string(row.directive) + " " + row.dist_spec);
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n" + std::string(kDistSignals) + kDistDeclarations + "  " +
          Statement(row.directive, row.dist_spec, "dist") + "\n  " +
          Statement(row.directive, row.inside_spec, "inside") + "\nendmodule\n",
      f);
  EXPECT_EQ((Counts{Count(out, "dist pass\n"), Count(out, "dist fail\n")}),
            row.counts);
  EXPECT_EQ((Counts{Count(out, "inside pass\n"), Count(out, "inside fail\n")}),
            row.counts);
  EXPECT_EQ(out.find("warning"), std::string::npos);
}

constexpr DistRow kDistForms[] = {
    {"assert property",
     "@(posedge clk) v dist {[2:3] :/ 60}",
     "@(posedge clk) v inside {[2:3]}",
     {2, 4}},
    {"assert property",
     "@(posedge clk) v dist {2 :/ 5, 4 :/ 5}",
     "@(posedge clk) v inside {2, 4}",
     {2, 4}},
    {"assert property",
     "@(posedge clk) v dist {2 := 0, 3 := 0}",
     "@(posedge clk) v inside {2, 3}",
     {2, 4}},
    {"assert property",
     "@(posedge clk) v dist {[3 +/- 1] := 1}",
     "@(posedge clk) v inside {[2:4]}",
     {3, 3}},
    {"assert property",
     "@(posedge clk) v dist {[4 +%- 50] := 1}",
     "@(posedge clk) v inside {[2:6]}",
     {5, 1}},
    {"assert property",
     "@(posedge clk) r dist {[1.0:2.0] :/ 1}",
     "@(posedge clk) r inside {[1.0:2.0]}",
     {3, 3}},
    {"cover property",
     "@(posedge clk) r dist {1.5 := 1, 2.5 := 1}",
     "@(posedge clk) r inside {1.5, 2.5}",
     {2, 0}},
    {"cover sequence",
     "@(posedge clk) v dist {1 := 1, 4 := 9}",
     "@(posedge clk) v inside {1, 4}",
     {2, 0}},
    {"assert property",
     "@(posedge clk) (v == 1) ##1 v dist {2 := 5}",
     "@(posedge clk) (v == 1) ##1 v inside {2}",
     {1, 5}},
    {"cover property",
     "@(posedge clk) (v == 1) ##1 v dist {2 := 5}",
     "@(posedge clk) (v == 1) ##1 v inside {2}",
     {1, 0}},
    {"cover sequence",
     "@(posedge clk) v dist {[2:5] := 1} [*2]",
     "@(posedge clk) v inside {[2:5]} [*2]",
     {3, 0}},
    {"cover sequence",
     "@(posedge clk) v dist {[1:6] := 1} throughout (v == 2 ##1 v == 3)",
     "@(posedge clk) v inside {[1:6]} throughout (v == 2 ##1 v == 3)",
     {1, 0}},
    {"assert property",
     "@(posedge clk) disable iff (v dist {5 := 1, 6 := 1}) 1",
     "@(posedge clk) disable iff (v inside {5, 6}) 1",
     {4, 0}},
    {"cover sequence",
     "@(posedge clk) disable iff (v dist {1 := 1, 2 := 1}) 1",
     "@(posedge clk) disable iff (v inside {1, 2}) 1",
     {4, 0}},
    {"assert property",
     "@(posedge clk) if (v dist {2 := 1, 5 := 1}) 1 else 0",
     "@(posedge clk) if (v inside {2, 5}) 1 else 0",
     {2, 4}},
    {"assert property",
     "@(posedge clk) case (v dist {2 := 1, 3 := 1}) 1'b1: 1; default: 0; "
     "endcase",
     "@(posedge clk) case (v inside {2, 3}) 1'b1: 1; default: 0; endcase",
     {2, 4}},
    {"assert property", "@(posedge clk) s1", "@(posedge clk) s1i", {2, 4}},
    {"assert property", "p1", "p1i", {1, 5}},
    {"assume property",
     "@(posedge clk) v dist {[2:3] :/ 60}",
     "@(posedge clk) v inside {[2:3]}",
     {2, 4}},
    {"assume property",
     "@(posedge clk) (v == 1) ##1 v dist {2 := 5}",
     "@(posedge clk) (v == 1) ##1 v inside {2}",
     {1, 5}}};

TEST(DistAsInside, EachDistFormIsReadAsTheInsideOperator) {
  for (const DistRow& row : kDistForms) ExpectDistReadAsInside(row);
}

TEST(DistAsInside, DISABLED_ADistCaseItemOfAPropertyCaseIsReadAsInside) {
  ExpectDistReadAsInside(
      {"assert property",
       "@(posedge clk) case (1'b1) v dist {2 := 1, 3 := 1}: 1; default: 0; "
       "endcase",
       "@(posedge clk) case (1'b1) v inside {2, 3}: 1; default: 0; endcase",
       {2, 4}});
}

constexpr const char* kDistPorts = "(input logic clk, input var int v)";

std::string DistPlaceSource(const std::string& place,
                            const std::string& items) {
  std::string top = "module t;\n" + std::string(kDistSignals);
  if (place == "module") return top + "  " + items + "\nendmodule\n";
  if (place == "always") {
    return top + "  always @(posedge clk) " + items + "\nendmodule\n";
  }
  if (place == "initial") {
    return top + "  initial begin #12; " + items + " end\nendmodule\n";
  }
  if (place == "generate") {
    return top + "  if (1) begin : g\n    " + items + "\n  end\nendmodule\n";
  }
  std::string header = place == "checker" ? "checker w(logic clk, int v);\n"
                                          : place + " w" + kDistPorts + ";\n";
  return header + "  " + items + "\nend" + place + "\n" + top +
         "  w u(clk, v);\nendmodule\n";
}

constexpr const char* kDistPlaces[] = {"module",   "always",    "initial",
                                       "generate", "interface", "program",
                                       "checker"};

constexpr const char* kPlacedDirectives[] = {
    "assert property", "assume property", "cover property"};

Counts PlacedCounts(const std::string& src, const std::string& tag) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  return {Count(out, tag + " pass\n"), Count(out, tag + " fail\n")};
}

void ExpectDistReadAsInsideIn(const std::string& place,
                              const std::string& directive) {
  SCOPED_TRACE(place + " " + directive);
  bool once = place == "initial";
  bool cover = directive.starts_with("cover");
  Counts want{once ? 1u : 2u, cover || once ? 0u : 4u};
  EXPECT_EQ(PlacedCounts(
                DistPlaceSource(
                    place, Statement(directive,
                                     "@(posedge clk) v dist {2 := 1, 3 := 1}",
                                     "dist")),
                "dist"),
            want);
}

TEST(DistAsInside, ADistIsReadAsInsideInEachPlace) {
  for (const char* place : kDistPlaces) {
    for (const char* directive : kPlacedDirectives) {
      ExpectDistReadAsInsideIn(place, directive);
    }
  }
}

TEST(DistAsInside, DISABLED_ADistIsReadAsInsideThroughAnUntypedCheckerFormal) {
  std::string src = DistPlaceSource(
      "checker", Statement("assert property",
                           "@(posedge clk) v dist {2 := 1, 3 := 1}", "dist"));
  src.replace(src.find("checker w(logic clk, int v);"),
              std::string("checker w(logic clk, int v);").size(),
              "checker w(clk, v);");
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_EQ((Counts{Count(out, "dist pass\n"), Count(out, "dist fail\n")}),
            (Counts{2, 4}));
}

struct ActionControlRow {
  const char* control;
  Counts counts;
};

constexpr ActionControlRow kActionControls[] = {{"", {2, 4}},
                                                {"$assertpassoff;", {0, 4}},
                                                {"$assertfailoff;", {2, 0}},
                                                {"$assertcontrol(7);", {0, 4}},
                                                {"$assertcontrol(9);", {2, 0}}};

void ExpectActionControlIn(const ActionControlRow& row,
                           const std::string& place,
                           const std::string& directive) {
  SCOPED_TRACE(std::string(row.control) + " " + place + " " + directive);
  std::string src = DistPlaceSource(
      place, Statement(directive, "@(posedge clk) v inside {2, 3}", "act"));
  src.insert(src.rfind("endmodule"),
             std::string("  initial begin ") + row.control + " end\n");
  EXPECT_EQ(PlacedCounts(src, "act"), row.counts);
}

constexpr const char* kCheckedDirectives[] = {"assert property",
                                              "assume property"};

TEST(AssumeActionControl,
     PassAndFailStatementsAreSilencedByTheirActionControlInEachPlace) {
  for (const ActionControlRow& row : kActionControls) {
    for (const char* place : kDistPlaces) {
      if (std::string(place) == "initial") continue;
      for (const char* directive : kCheckedDirectives) {
        ExpectActionControlIn(row, place, directive);
      }
    }
  }
}

}  // namespace
