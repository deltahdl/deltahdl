#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_2_EquivalentSpecifications) {

  auto pp = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(pp.has_errors);

  auto pr = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(pr.has_errors);

  EXPECT_EQ(pp.timescale.unit, pr.cu->modules[0]->time_unit);
  EXPECT_EQ(pp.timescale.precision, pr.cu->modules[0]->time_prec);
}

}
