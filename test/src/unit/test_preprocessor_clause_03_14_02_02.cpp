// §3.14.2.2: The timeunit and timeprecision keywords

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM §3.14 — Simulation time units and precision
// =============================================================================
TEST(ParserClause03, Cl3_14_TimeunitsAndTimescale) {
  auto r1 = ParseWithPreprocessor("module m; timeunit 1ns; endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_TRUE(r1.cu->modules[0]->has_timeunit);
  auto r2 = ParseWithPreprocessor("module m; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_TRUE(r2.cu->modules[0]->has_timeprecision);
  auto r3 = ParseWithPreprocessor(
      "module m; timeunit 1ns; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r3.has_errors);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeprecision);
  EXPECT_TRUE(ParseOk("module m; timeunit 100ps / 10fs; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("program p; timeunit 10us; timeprecision 100ns; endprogram\n"));
  EXPECT_TRUE(ParseOk("interface ifc; timeunit 1ns; endinterface\n"));
  // `timescale directive
  EXPECT_TRUE(ParseOk("`timescale 1ns/1ps\nmodule m; endmodule\n"));
  // Time literals (§5.8): integer, fractional, all unit suffixes
  EXPECT_TRUE(ParseOk("module m; initial #10ns $display(\"d\"); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns $display(\"d\"); endmodule\n"));
  // Various magnitudes (Table 3-1)
  EXPECT_TRUE(
      ParseOk("module a; timeunit 100ns; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module b; timeunit 1us; timeprecision 1ns; endmodule\n"));
}

// 13. Time values stored in design element: module with timeunit and
// timeprecision stores both components.
TEST(ParserClause03, Cl3_14_TimeValuesInDesignElement) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

}  // namespace
