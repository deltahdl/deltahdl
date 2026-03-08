// §10.10.2

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §10.10.2: Concatenation braces disambiguate based on target type.
TEST(ElabCh10j, ConcatBracesDisambiguateByTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte B;\n"
      "  byte BA[2];\n"
      "  initial begin\n"
      "    B = {4'h6, 4'hf};\n"
      "    BA = {4'h6, 4'hf};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
