#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A UDP that is instantiated before its definition appears in the source
// must still be recognized as a UDP instance during elaboration; the
// elaborator should not emit "unknown module" for the forward reference.
TEST(UdpForwardReferenceElaboration, UdpDefinedAfterInstantiationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp u1(y, a);\n"
      "endmodule\n"
      "primitive my_udp(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Two modules instantiate the same UDP with opposite source orderings
// relative to the UDP definition; both must elaborate without errors.
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

}  // namespace
