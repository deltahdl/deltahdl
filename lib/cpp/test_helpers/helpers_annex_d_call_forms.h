#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

inline void ExpectOnlyTheMalformedCallReported(const std::string& well_formed,
                                               const std::string& malformed,
                                               const std::string& message,
                                               const std::string& sub) {
  std::string src =
      "module t;\n"
      "  int v;\n"
      "  initial begin\n"
      "    ";
  src += well_formed;
  src += ";\n    ";
  src += malformed;
  src +=
      ";\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "    " + malformed + ";"), sub))
      << src;
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), message,
                             LineHolding(src, "    " + well_formed + ";"), sub))
      << src;
}
