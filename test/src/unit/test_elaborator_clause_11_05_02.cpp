
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayAddressingElaboration, WriteAndReadArrayElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ArrayAddressingElaboration, MultiDimArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:3][0:3];\n"
             "  int result;\n"
             "  initial result = mem[1][2];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, MemoryIndirectionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:7];\n"
             "  int result;\n"
             "  initial result = mem[mem[3]];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, BitSelectAfterArrayElementElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:3];\n"
             "  logic result;\n"
             "  initial result = arr[2][5];\n"
             "endmodule\n"));
}

// §11.5.2 — a bit-select or part-select of an array element requires an address
// for every dimension first. Addressing all dimensions, then part-selecting the
// selected word, is legal.
TEST(ArrayAddressingElaboration, PartSelectAfterAllDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] twod [0:3][0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = twod[1][2][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 — the positive boundary for a three-dimensional array: once all three
// dimensions are addressed the selected item is a vector, so a part-select of
// it is legal. This is the accepting twin of the rejections below.
TEST(ArrayAddressingElaboration, PartSelectAfterAllThreeDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][0][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 — the part-select here reaches the third dimension before it has been
// addressed (only two of the three dimensions are indexed), which is illegal.
TEST(ArrayAddressingElaboration,
     PartSelectBeforeAllDimensionsAddressedIsIllegal) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 — the same rule applies to the indexed part-select form: leaving a
// dimension unaddressed and then applying an indexed part-select is illegal.
TEST(ArrayAddressingElaboration,
     IndexedPartSelectBeforeAllDimensionsAddressedIsIllegal) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][0 +: 4];\n"
             "endmodule\n"));
}

// §11.5.2 — the descending indexed part-select form (-:) is likewise rejected
// when a dimension is left unaddressed; the rule covers every part-select shape
// of 11.5.1, not just the range and ascending-indexed forms.
TEST(ArrayAddressingElaboration,
     DescendingIndexedPartSelectBeforeAllDimensionsAddressedIsIllegal) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][3 -: 4];\n"
             "endmodule\n"));
}

}  // namespace
