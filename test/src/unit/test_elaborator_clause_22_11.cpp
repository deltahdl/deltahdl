#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PragmaElaboration, MultiplePragmasElaborate) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`pragma first_pragma\n"
      "module t;\n"
      "  `pragma second_pragma 42\n"
      "  parameter P = 5;\n"
      "endmodule\n"
      "`pragma third_pragma\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
