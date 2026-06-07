#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §22.10 has no elaborator-stage rule: the directives are consumed by the
// preprocessor, so a cell module reaches the elaborator as an ordinary module.
// One representative check that such a module elaborates cleanly is sufficient;
// the directive-pairing/placement variations are observed in the preprocessor
// tests.
TEST(CelldefineElaboration, CelldefineModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`celldefine\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
