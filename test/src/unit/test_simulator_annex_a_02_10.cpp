#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A.2.10 with A.9.3 and §26.3: a package's property or sequence instance
// standing alone as the spec runs as the same instance declared in the
// module does. clk, the package's, rises at 5, 15, 25, 35 and 45 and a is 1,
// so each assertion passes and each cover matches five times by 47: the
// expect statement waits for the first tick at 5, and the display follows
// it by 42. The named property r, whose body is the package instance, and
// the instances called by name and with no list run the same, and the
// expect statement passes once.
TEST(PackageInstanceSpecRun, APackageInstanceAloneRunsAsTheModulesWould) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  bit clk;\n"
      "  sequence s(a); @(posedge clk) a; endsequence\n"
      "  property q(a); @(posedge clk) a; endproperty\n"
      "  property q0; @(posedge clk) 1; endproperty\n"
      "endpackage\n"
      "module m;\n"
      "  logic a = 1, x = 1;\n"
      "  int n[10];\n"
      "  always #5 pk::clk = ~pk::clk;\n"
      "  property r; pk::q(a); endproperty\n"
      "  assert property (pk::q(a)) n[0]++;\n"
      "  assert property (pk::s(a)) n[1]++;\n"
      "  assume property (pk::q(a)) n[2]++;\n"
      "  cover property (pk::q(a)) n[3]++;\n"
      "  cover sequence (pk::s(a)) n[4]++;\n"
      "  restrict property (pk::q(a));\n"
      "  assert property (pk::q0) n[5]++;\n"
      "  assert property (pk::q(.a(x))) n[6]++;\n"
      "  assert property (r) n[7]++;\n"
      "  cover property (pk::q0) n[8]++;\n"
      "  initial begin\n"
      "    expect (pk::q(a)) n[9]++;\n"
      "    #42;\n"
      "    foreach (n[i]) $write(\"%0d \", n[i]);\n"
      "    $display;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("5 5 5 5 5 5 5 5 5 1 \n"), std::string::npos) << out;
}

// The contrast: a package property whose clock is written on the
// module's posedge clk and whose a is 0 at every tick fails, so the
// instance alone is not merely accepted but evaluated, failing at 5, 15,
// 25 and 35 before 42.
TEST(PackageInstanceSpecRun, APackageInstanceAloneFailsWhereItsBodyDoes) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  property q(a, c); @(posedge c) a; endproperty\n"
      "endpackage\n"
      "module m;\n"
      "  logic clk = 0, a = 0;\n"
      "  int nf;\n"
      "  always #5 clk = ~clk;\n"
      "  assert property (pk::q(a, clk)) else nf++;\n"
      "  initial #42 begin\n"
      "    $display(\"%0d\", nf);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4\n"), std::string::npos) << out;
}

}  // namespace
