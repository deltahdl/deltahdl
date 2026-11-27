#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MailboxOfTypeReferenceSim, CarriesAByte) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  mailbox #(type(byte)) m = new;\n"
                       "  byte b;\n"
                       "  initial begin\n"
                       "    m.put(8'd200);\n"
                       "    m.get(b);\n"
                       "    $display(\"%0d\", b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-56\n");
}

TEST(MailboxOfTypeReferenceSim, WeakReferenceOfAHandlesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K; int m = 5; endclass\n"
                       "module top;\n"
                       "  K k;\n"
                       "  weak_reference #(type(k)) w;\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    w = new(k);\n"
                       "    $display(\"%0d\", w.get().m);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ScopeDeclarationTypeRefSim, PackageAndUnitVariablesTakeTheReferencedType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  logic [7:0] pb;\n"
                 "  int pa [4];\n"
                 "  var type(pb) pv;\n"
                 "  var type(pb[3:0]) ps;\n"
                 "  var type(pa) pf;\n"
                 "  function automatic int pbits();\n"
                 "    return $bits(pv);\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "logic [11:0] ub;\n"
                 "var type(ub) uv;\n"
                 "var type(ub + 4'b0) ue;\n"
                 "module top;\n"
                 "  logic [5:0] mb;\n"
                 "  var type(mb) mv;\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", "
                 "$bits(pk::pv), pk::pbits(), $bits(pk::ps), "
                 "$size(pk::pf), $bits(uv), $bits(ue), $isunknown(uv), "
                 "$bits(mv));\n"
                 "endmodule\n",
                 f),
      "8 8 4 4 12 12 1 6\n");
}

}  // namespace
