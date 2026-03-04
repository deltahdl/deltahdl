// §3.14.2: Specifying time units and precision

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 30. Equivalent specifications: both mechanisms specify the same time values.
// `timescale 1ns/1ps is equivalent to timeunit 1ns; timeprecision 1ps.
TEST(ParserClause03, Cl3_14_2_EquivalentSpecifications) {
  // Way 1: `timescale directive.
  auto pp = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(pp.has_errors);
  // Way 2: keywords inside a module.
  auto pr = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(pr.has_errors);
  // Both specify the same unit and precision.
  EXPECT_EQ(pp.timescale.unit, pr.cu->modules[0]->time_unit);
  EXPECT_EQ(pp.timescale.precision, pr.cu->modules[0]->time_prec);
}

}  // namespace
