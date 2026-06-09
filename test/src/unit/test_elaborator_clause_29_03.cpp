#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §29.3: a UDP may be instantiated before or after its definition in the
// source text. This single test covers both directions in one design --
// before_def references the UDP defined later (forward reference) and
// after_def references it from earlier in the file -- so a separate
// forward-only case would re-exercise the same order-independent resolution.
TEST(UdpForwardReferenceElaboration, UdpReferencedBeforeAndAfterDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module before_def;\n"
      "  wire y, a;\n"
      "  inv u1(y, a);\n"
      "endmodule\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module after_def;\n"
      "  wire y, a;\n"
      "  inv u2(y, a);\n"
      "endmodule\n",
      f, "before_def");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
