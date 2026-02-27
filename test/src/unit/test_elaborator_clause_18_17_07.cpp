// §18.17.7: Value passing between productions

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Randsequence with production ports and return types elaborates
TEST(ElabA612, ProductionPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(5);\n"
      "      void gen(int x) : { $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
