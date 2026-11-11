#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassStructSim, StructHoldsItsOwnValueWhileAHandleSharesItsObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class D; int a; endclass\n"
      "typedef struct { int a; } st_t;\n"
      "module m;\n"
      "  st_t s, s2;\n"
      "  D d, d2;\n"
      "  int r1, r2, r3, r4, r5;\n"
      "  initial begin\n"
      "    s.a = 5;\n"
      "    s2 = s;\n"
      "    s2.a = 6;\n"
      "    r1 = s.a;\n"
      "    r2 = s2.a;\n"
      "    r3 = (d == null);\n"
      "    d = new;\n"
      "    d.a = 7;\n"
      "    d2 = d;\n"
      "    d2.a = 9;\n"
      "    r4 = d.a;\n"
      "    r5 = (d == d2);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 5u}, {"r2", 6u}, {"r3", 1u}, {"r4", 9u}, {"r5", 1u}});
}

}  // namespace
