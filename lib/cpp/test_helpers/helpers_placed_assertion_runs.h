#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

struct PlacedDesign {
  const char* signals;
  const char* ports;
  const char* port_names;
};

inline constexpr const char* kAssertionPlaces[] = {
    "module",    "always",  "initial", "generate",
    "interface", "program", "checker"};

inline std::string PlacedIndented(const std::string& lines,
                                  const std::string& prefix,
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

inline std::string PlacedTop(const PlacedDesign& design,
                             const std::string& items,
                             const std::string& controls) {
  std::string out = "module t;\n" + std::string(design.signals) + items;
  if (!controls.empty()) out += "  initial begin " + controls + " end\n";
  return out + "endmodule\n";
}

inline std::string PlacedSource(const PlacedDesign& design,
                                const std::string& place,
                                const std::string& items,
                                const std::string& declarations = "",
                                const std::string& controls = "") {
  std::string decl = PlacedIndented(declarations, "", "");
  if (place == "module") {
    return PlacedTop(design, decl + PlacedIndented(items, "", ""), controls);
  }
  if (place == "always") {
    return PlacedTop(design,
                     decl + PlacedIndented(items, "always @(posedge clk) ", ""),
                     controls);
  }
  if (place == "initial") {
    return PlacedTop(
        design, decl + PlacedIndented(items, "initial begin #12; ", " end"),
        controls);
  }
  if (place == "generate") {
    return PlacedTop(design,
                     "  if (1) begin : g\n" + decl +
                         PlacedIndented(items, "", "") + "  end\n",
                     controls);
  }
  std::string names = design.port_names;
  std::string header = place == "checker" ? "checker w(" + names + ");\n"
                                          : place + " w" + design.ports + ";\n";
  return header + decl + PlacedIndented(items, "", "") + "end" + place + "\n" +
         PlacedTop(design, "  w u(" + names + ");\n", controls);
}

inline std::string PlacedScope(const std::string& place) {
  if (place == "generate") return "t.g";
  if (place == "interface" || place == "program" || place == "checker") {
    return "t.u";
  }
  return "t";
}

inline std::vector<std::string> PlacedLines(const std::string& text) {
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

inline std::string PlacedWithoutLocation(const std::string& line) {
  if (line.empty() || line[0] != '[') return line;
  size_t open = line.find(" (");
  size_t close = line.find(')', open);
  if (open == std::string::npos || close == std::string::npos) return line;
  return line.substr(0, open) + line.substr(close + 1);
}

inline std::string PlacedSorted(std::vector<std::string> lines) {
  std::sort(lines.begin(), lines.end());
  std::string out;
  for (const std::string& line : lines) out += line + "\n";
  return out;
}

inline std::string PlacedSortedVerdicts(const std::string& text) {
  std::vector<std::string> kept;
  for (const std::string& line : PlacedLines(text)) {
    if (!line.starts_with("$finish") && !line.starts_with("cover ")) {
      kept.push_back(line);
    }
  }
  return PlacedSorted(kept);
}

struct PlacedRun {
  std::string lines;
  std::string out;
};

inline PlacedRun RunPlaced(const std::string& src, SimFixture& f) {
  testing::internal::CaptureStderr();
  std::string out = RunCapture(src, f);
  std::string err = testing::internal::GetCapturedStderr();
  std::vector<std::string> kept;
  for (const std::string& line : PlacedLines(out + err)) {
    if (line.starts_with("$finish")) continue;
    kept.push_back(PlacedWithoutLocation(line));
  }
  return {PlacedSorted(kept), out};
}

inline PlacedRun RunPlaced(const std::string& src) {
  SimFixture f;
  return RunPlaced(src, f);
}

inline std::string PlacedExpected(const std::string& text,
                                  const std::string& scope) {
  std::string out = text;
  for (size_t at = out.find('%'); at != std::string::npos;
       at = out.find('%', at + scope.size())) {
    out.replace(at, 1, scope);
  }
  return PlacedSorted(PlacedLines(out));
}

struct PlacedRow {
  const char* items;
  const char* everywhere;
  const char* in_initial;
};

inline void ExpectPlacedLinesInEachPlace(const PlacedDesign& design,
                                         const PlacedRow& row,
                                         const std::string& declarations = "",
                                         const std::string& controls = "") {
  for (const char* place : kAssertionPlaces) {
    SCOPED_TRACE(std::string(place) + ": " + row.items);
    const char* want = std::string(place) == "initial" && row.in_initial
                           ? row.in_initial
                           : row.everywhere;
    EXPECT_EQ(RunPlaced(PlacedSource(design, place, row.items, declarations,
                                     controls))
                  .lines,
              PlacedExpected(want, PlacedScope(place)));
  }
}
