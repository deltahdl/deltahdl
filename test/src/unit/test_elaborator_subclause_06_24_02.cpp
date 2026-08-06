#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.24.2: the task form of $cast performs no type checking at compile time;
// an assignment that the type system would otherwise reject (here, an integer
// that is not a member of the enum) must elaborate without a diagnostic.
TEST(DynamicCastElaboration, TaskFormNoCompileTimeTypeCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial $cast(c, 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.2: the function form of $cast never issues a compile-time error, even
// when the source value is not assignment valid for the destination type.
TEST(DynamicCastElaboration, FunctionFormNoCompileTimeError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial ok = $cast(c, 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
