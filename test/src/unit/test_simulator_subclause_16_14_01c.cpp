#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kActionSignals =
    "  logic clk = 0, a = 1, d = 0, e = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin #10 a = 0; #10 a = 1; #20 $finish; end\n"
    "  initial begin #12 d = 1; #6 d = 0; #14 e = 1; #6 e = 0; end\n"
    "  int marker = -1;\n"
    "  always @(posedge clk) marker = $time;\n";

constexpr const char* kActionPorts = "(input logic clk, a, d, e)";

constexpr const char* kActionPlaces[] = {"module",   "always",    "initial",
                                         "generate", "interface", "program",
                                         "checker"};

std::string Indented(const std::string& lines, const std::string& prefix,
                     const std::string& suffix) {
  std::string out;
  size_t at = 0;
  while (at < lines.size()) {
    size_t end = lines.find('\n', at);
    out.append("  ").append(prefix).append(lines, at, end - at);
    out.append(suffix).append("\n");
    at = end + 1;
  }
  return out;
}

std::string ActionTop(const std::string& items, const std::string& controls) {
  std::string out = "module t;\n" + std::string(kActionSignals) + items;
  if (!controls.empty()) out += "  initial begin " + controls + " end\n";
  return out + "endmodule\n";
}

std::string ActionSource(const std::string& place, const std::string& items,
                         const std::string& declarations = "",
                         const std::string& controls = "") {
  std::string decl = Indented(declarations, "", "");
  if (place == "module")
    return ActionTop(decl + Indented(items, "", ""), controls);
  if (place == "always") {
    return ActionTop(decl + Indented(items, "always @(posedge clk) ", ""),
                     controls);
  }
  if (place == "initial") {
    return ActionTop(decl + Indented(items, "initial begin #12; ", " end"),
                     controls);
  }
  if (place == "generate") {
    return ActionTop(
        "  if (1) begin : g\n" + decl + Indented(items, "", "") + "  end\n",
        controls);
  }
  std::string header = place == "checker" ? "checker w(clk, a, d, e);\n"
                                          : place + " w" + kActionPorts + ";\n";
  return header + decl + Indented(items, "", "") + "end" + place + "\n" +
         ActionTop("  w u(clk, a, d, e);\n", controls);
}

std::string ScopeOf(const std::string& place) {
  if (place == "generate") return "t.g";
  if (place == "interface" || place == "program" || place == "checker") {
    return "t.u";
  }
  return "t";
}

std::vector<std::string> LinesOf(const std::string& text) {
  std::vector<std::string> lines;
  size_t at = 0;
  while (at < text.size()) {
    size_t end = text.find('\n', at);
    if (end == std::string::npos) end = text.size();
    if (end > at) lines.push_back(text.substr(at, end - at));
    at = end + 1;
  }
  return lines;
}

std::string WithoutLocation(const std::string& line) {
  if (line.empty() || line[0] != '[') return line;
  size_t open = line.find(" (");
  size_t close = line.find(')', open);
  if (open == std::string::npos || close == std::string::npos) return line;
  return line.substr(0, open) + line.substr(close + 1);
}

std::string Sorted(std::vector<std::string> lines) {
  std::sort(lines.begin(), lines.end());
  std::string out;
  for (const std::string& line : lines) out += line + "\n";
  return out;
}

struct ActionRun {
  std::string lines;
  std::string out;
};

ActionRun RunActions(const std::string& src) {
  SimFixture f;
  testing::internal::CaptureStderr();
  std::string out = RunCapture(src, f);
  std::string err = testing::internal::GetCapturedStderr();
  std::vector<std::string> kept;
  for (const std::string& line : LinesOf(out + err)) {
    if (line.starts_with("$finish")) continue;
    kept.push_back(WithoutLocation(line));
  }
  return {Sorted(kept), out};
}

std::string Expected(const std::string& text, const std::string& scope) {
  std::string out = text;
  for (size_t at = out.find('%'); at != std::string::npos;
       at = out.find('%', at + scope.size())) {
    out.replace(at, 1, scope);
  }
  return Sorted(LinesOf(out));
}

struct PlacedRow {
  const char* items;
  const char* everywhere;
  const char* in_initial;
};

void ExpectLinesInEachPlace(const PlacedRow& row,
                            const std::string& declarations = "") {
  for (const char* place : kActionPlaces) {
    SCOPED_TRACE(std::string(place) + ": " + row.items);
    const char* want = std::string(place) == "initial" && row.in_initial
                           ? row.in_initial
                           : row.everywhere;
    EXPECT_EQ(RunActions(ActionSource(place, row.items, declarations)).lines,
              Expected(want, ScopeOf(place)));
  }
}

TEST(AssertDefaultReport,
     EachFailingAssertOrAssumeWithoutAnElseReportsAnErrorInEachPlace) {
  ExpectLinesInEachPlace(
      {"a1: assert property (@(posedge clk) a);\n"
       "u1: assume property (@(posedge clk) a);\n",
       "[15] ERROR %.a1: Assertion failed.\n"
       "[15] ERROR %.u1: Assertion failed.\n",
       nullptr});
}

TEST(AssertDefaultReport,
     APassingADisabledOrANullElseAttemptReportsNothingInEachPlace) {
  ExpectLinesInEachPlace(
      {"p1: assert property (@(posedge clk) 1);\n"
       "p2: assume property (@(posedge clk) 1);\n"
       "d1: assert property (@(posedge clk) disable iff (d) a);\n"
       "d2: assume property (@(posedge clk) disable iff (d) a);\n"
       "n1: assert property (@(posedge clk) a) else ;\n"
       "n2: assume property (@(posedge clk) a) else ;\n",
       "", nullptr});
}

TEST(AssertActionChoice,
     PassAndFailStatementsFollowTheVerdictAndADisabledAttemptRunsNeither) {
  ExpectLinesInEachPlace(
      {"pa: assert property (@(posedge clk) disable iff (e) a) "
       "$display(\"assert pass %0t\", $time); "
       "else $display(\"assert fail %0t\", $time);\n"
       "pu: assume property (@(posedge clk) disable iff (e) a) "
       "$display(\"assume pass %0t\", $time); "
       "else $display(\"assume fail %0t\", $time);\n",
       "assert pass 5\nassert fail 15\nassert pass 25\n"
       "assume pass 5\nassume fail 15\nassume pass 25\n",
       "assert fail 15\nassume fail 15\n"});
}

TEST(AssertActionChoice, TheActionBlockRunsInTheReactiveRegionInEachPlace) {
  ExpectLinesInEachPlace(
      {"rx: assert property (@(posedge clk) 1) "
       "if (t.marker == $time) $display(\"reactive %0t\", $time);\n",
       "reactive 5\nreactive 15\nreactive 25\nreactive 35\n", "reactive 15\n"});
}

struct ControlRow {
  const char* controls;
  const char* reports;
};

constexpr const char* kTwoDefaultFailures =
    "a1: assert property (@(posedge clk) a);\n"
    "u1: assume property (@(posedge clk) a);\n";

constexpr const char* kBothReported =
    "[15] ERROR t.a1: Assertion failed.\n[15] ERROR t.u1: Assertion failed.\n";

constexpr ControlRow kControls[] = {
    {"$assertfailoff;", ""},
    {"$assertcontrol(9);", ""},
    {"$assertoff;", ""},
    {"$assertkill;", ""},
    {"$assertcontrol(4);", ""},
    {"$assertcontrol(5);", ""},
    {"$assertfailoff; #12 $assertfailon;", kBothReported},
    {"$assertfailoff; #12 $assertcontrol(8);", kBothReported},
    {"$assertcontrol(9, 1, 4);", "[15] ERROR t.a1: Assertion failed.\n"},
    {"$assertcontrol(9, 1, 1);", "[15] ERROR t.u1: Assertion failed.\n"},
    {"$assertcontrol(9, 30);", kBothReported},
    {"$assertcontrol(9, 1);", ""}};

TEST(AssertDefaultReport, EachControlThatSuppressesTheFailureSilencesIt) {
  for (const ControlRow& row : kControls) {
    SCOPED_TRACE(row.controls);
    EXPECT_EQ(RunActions(
                  ActionSource("module", kTwoDefaultFailures, "", row.controls))
                  .lines,
              Expected(row.reports, "t"));
  }
}

TEST(AssertDefaultReport, FailOffSilencesTheDefaultReportInEachPlace) {
  for (const char* place : kActionPlaces) {
    SCOPED_TRACE(place);
    EXPECT_EQ(RunActions(ActionSource(place, kTwoDefaultFailures, "",
                                      "$assertfailoff;"))
                  .lines,
              "");
  }
}

TEST(AssertDefaultReport, AScopedFailOffSilencesOnlyThatScope) {
  EXPECT_EQ(RunActions(ActionSource("module",
                                    "a1: assert property (@(posedge clk) a);\n"
                                    "if (1) begin : g ga: assert property "
                                    "(@(posedge clk) a); end\n",
                                    "", "$assertfailoff(0, t.g);"))
                .lines,
            Expected("[15] ERROR t.a1: Assertion failed.\n", "t"));
}

TEST(AssertSeverityTask, EachSeverityTaskInAFailStatementReportsItsSeverity) {
  ExpectLinesInEachPlace(
      {"w1: assert property (@(posedge clk) a) else $warning(\"w1\");\n"
       "i1: assert property (@(posedge clk) a) else $info(\"i1\");\n"
       "e1: assert property (@(posedge clk) a) else $error(\"e1\");\n"
       "w2: assume property (@(posedge clk) a) else $warning(\"w2\");\n"
       "i2: assume property (@(posedge clk) a) else $info(\"i2\");\n"
       "e2: assume property (@(posedge clk) a) else $error(\"e2\");\n",
       "[15] WARNING %.w1: w1\n[15] INFO %.i1: i1\n[15] ERROR %.e1: e1\n"
       "[15] WARNING %.w2: w2\n[15] INFO %.i2: i2\n[15] ERROR %.e2: e2\n",
       nullptr});
}

TEST(AssertSeverityTask, EachSeverityTaskInAPassStatementReportsItsSeverity) {
  ExpectLinesInEachPlace(
      {"pi: assert property (@(posedge clk) a) $info(\"pi\");\n"
       "pw: assert property (@(posedge clk) a) $warning(\"pw\");\n"
       "pe: assert property (@(posedge clk) a) $error(\"pe\");\n"
       "ui: assume property (@(posedge clk) a) $info(\"ui\");\n"
       "uw: assume property (@(posedge clk) a) $warning(\"uw\");\n"
       "ci: cover property (@(posedge clk) !a) $info(\"ci\");\n"
       "cs: cover sequence (@(posedge clk) !a) $warning(\"cs\");\n",
       "[5] INFO %.pi: pi\n[15] ERROR %.pi: Assertion failed.\n"
       "[25] INFO %.pi: pi\n[35] INFO %.pi: pi\n"
       "[5] WARNING %.pw: pw\n[15] ERROR %.pw: Assertion failed.\n"
       "[25] WARNING %.pw: pw\n[35] WARNING %.pw: pw\n"
       "[5] ERROR %.pe: pe\n[15] ERROR %.pe: Assertion failed.\n"
       "[25] ERROR %.pe: pe\n[35] ERROR %.pe: pe\n"
       "[5] INFO %.ui: ui\n[15] ERROR %.ui: Assertion failed.\n"
       "[25] INFO %.ui: ui\n[35] INFO %.ui: ui\n"
       "[5] WARNING %.uw: uw\n[15] ERROR %.uw: Assertion failed.\n"
       "[25] WARNING %.uw: uw\n[35] WARNING %.uw: uw\n"
       "[15] INFO %.ci: ci\n[15] WARNING %.cs: cs\n",
       "[15] ERROR %.pi: Assertion failed.\n[15] ERROR %.pw: Assertion "
       "failed.\n"
       "[15] ERROR %.pe: Assertion failed.\n[15] ERROR %.ui: Assertion "
       "failed.\n"
       "[15] ERROR %.uw: Assertion failed.\n"
       "[15] INFO %.ci: ci\n[15] WARNING %.cs: cs\n"});
}

TEST(AssertSeverityTask, EachOfSeveralTasksInOneActionBlockReportsInOrder) {
  for (const char* place : kActionPlaces) {
    SCOPED_TRACE(place);
    ActionRun run = RunActions(
        ActionSource(place,
                     "m2: assert property (@(posedge clk) a) "
                     "else begin $warning(\"m-w\"); $info(\"m-i\"); end\n"));
    std::string scope = ScopeOf(place);
    EXPECT_EQ(run.lines,
              Expected("[15] WARNING %.m2: m-w\n[15] INFO %.m2: m-i\n", scope));
    EXPECT_LT(run.out.find("m-w"), run.out.find("m-i"));
  }
}

TEST(AssertSeverityTask, AFatalInAFailStatementEndsTheRunInEachPlace) {
  for (const char* place : kActionPlaces) {
    for (const char* directive : {"assert", "assume"}) {
      SCOPED_TRACE(std::string(place) + " " + directive);
      ActionRun run = RunActions(ActionSource(
          place, "f1: " + std::string(directive) +
                     " property (@(posedge clk) a) else $fatal(1, \"f1\");\n"));
      EXPECT_EQ(run.lines, Expected("[15] FATAL %.f1: f1\n", ScopeOf(place)));
      EXPECT_NE(run.out.find("$finish at time 15\n"), std::string::npos);
    }
  }
}

struct FatalRow {
  const char* items;
  const char* report;
  const char* ending;
};

constexpr FatalRow kFatalForms[] = {
    {"f0: assert property (@(posedge clk) a) else $fatal;\n",
     "[15] FATAL t.f0\n", "$finish at time 15\n"},
    {"f1: assert property (@(posedge clk) a) else $fatal(0, \"f1\");\n",
     "[15] FATAL t.f1: f1\n", ""},
    {"f2: assert property (@(posedge clk) a) else $fatal(2, \"f2\");\n",
     "[15] FATAL t.f2: f2\n",
     "$finish at time 15\n$finish: memory and CPU time statistics "
     "unavailable\n"},
    {"f3: assume property (@(posedge clk) a) else $fatal(1, \"f3\");\n",
     "[15] FATAL t.f3: f3\n", "$finish at time 15\n"},
    {"f4: assert property (@(posedge clk) a) $fatal(1, \"f4\");\n",
     "[5] FATAL t.f4: f4\n", "$finish at time 5\n"},
    {"f5: assume property (@(posedge clk) a) $fatal(1, \"f5\");\n",
     "[5] FATAL t.f5: f5\n", "$finish at time 5\n"}};

TEST(AssertSeverityTask, EachFatalFormEndsTheRunAsItsFinishNumberSays) {
  for (const FatalRow& row : kFatalForms) {
    SCOPED_TRACE(row.items);
    ActionRun run = RunActions(ActionSource("module", row.items));
    EXPECT_EQ(run.lines, Expected(row.report, "t"));
    std::string ending = row.ending;
    size_t from = run.out.find("$finish");
    EXPECT_EQ(from == std::string::npos ? "" : run.out.substr(from), ending);
  }
}

TEST(AssertSeverityTask, ATaskReadingTheFailureTimeReportsAtTheFailure) {
  ExpectLinesInEachPlace(
      {"dl: assert property (@(posedge clk) a) "
       "else begin ft = $time; $error(\"failed at %0t\", ft); end\n",
       "[15] ERROR %.dl: failed at 15\n", nullptr},
      "time ft;\n");
}

constexpr const char* kDelayedTask =
    "dl: assert property (@(posedge clk) a) "
    "else begin ft = $time; #3 $error(\"failed at %0t\", ft); end\n";

void ExpectDelayedTaskIn(const char* place) {
  SCOPED_TRACE(place);
  EXPECT_EQ(RunActions(ActionSource(place, kDelayedTask, "time ft;\n")).lines,
            Expected("[18] ERROR %.dl: failed at 15\n", ScopeOf(place)));
}

TEST(AssertSeverityTask, ATaskAfterADelayInAProcedureReportsWhenItRuns) {
  ExpectDelayedTaskIn("always");
  ExpectDelayedTaskIn("initial");
}

constexpr const char* kModuleLevelPlaces[] = {"module", "generate", "interface",
                                              "program", "checker"};

TEST(AssertSeverityTask,
     DISABLED_ATaskAfterADelayAtModuleLevelReportsWhenItRuns) {
  for (const char* place : kModuleLevelPlaces) ExpectDelayedTaskIn(place);
}

}  // namespace
