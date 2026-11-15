#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_expect_runs.h"

using namespace delta;

namespace {

constexpr const char* kMatchThenFail =
    "matched at 45\nafter at 45\nfailed at 55\nafter at 55\n"
    "$finish at time 210\n";

void ExpectTwiceOver(const std::string& spec, const std::string& declarations) {
  std::string expect = "    expect (" + spec +
                       ")\n"
                       "      $display(\"matched at %0d\", $time);\n"
                       "      else $display(\"failed at %0d\", $time);\n"
                       "    $display(\"after at %0d\", $time);\n";
  SimFixture f;
  std::string out = RunCapture(ExpectDesign(expect + expect, declarations), f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << spec;
  EXPECT_EQ(out, kMatchThenFail) << spec;
}

TEST(ExpectSpecRun, ANamedPropertyWithoutArguments) {
  ExpectTwiceOver("pn",
                  "  property pn; @(posedge clk) a ##1 b ##1 c; endproperty\n");
}

TEST(ExpectSpecRun, ANamedPropertyWithArguments) {
  ExpectTwiceOver("pa(a, b, c)",
                  "  property pa(x, y, z);\n"
                  "    @(posedge clk) x ##1 y ##1 z;\n"
                  "  endproperty\n");
}

TEST(ExpectSpecRun, ANamedSequenceWithoutArguments) {
  ExpectTwiceOver("sn",
                  "  sequence sn; @(posedge clk) a ##1 b ##1 c; endsequence\n");
}

TEST(ExpectSpecRun, ANamedSequenceWithArguments) {
  ExpectTwiceOver("sa(a, b, c)",
                  "  sequence sa(x, y, z);\n"
                  "    @(posedge clk) x ##1 y ##1 z;\n"
                  "  endsequence\n");
}

}  // namespace
