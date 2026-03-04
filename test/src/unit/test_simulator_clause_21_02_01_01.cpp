#include "fixture_simulator.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA82, SystemTaskDisplay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SysTask, FormatOctal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 8));
  auto out = FormatDisplay("%o", vals);
  EXPECT_EQ(out, "00000000010");
}

TEST(SysTask, FormatReal_e) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%e", vals);
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, FormatReal_f) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%f", vals);
  EXPECT_NE(out.find("2.5"), std::string::npos);
}

TEST(FormatArg, DecimalUnsigned) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 42);
  EXPECT_EQ(FormatArg(val, 'd'), "42");
}

}
