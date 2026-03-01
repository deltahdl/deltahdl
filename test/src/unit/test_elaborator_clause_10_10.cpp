// §10.10: Unpacked array concatenation

#include "builders_ast.h"
#include "fixture_enum_methods.h"
#include "fixture_evaluator.h"
#include "fixture_lexer.h"
#include "fixture_preprocessor.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// § empty_unpacked_array_concatenation elaborates
TEST(ElabA81, EmptyUnpackedArrayConcatElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
