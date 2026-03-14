#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §15.5.5: Event declaration with initializer shares the Variable object.
TEST(IpcSync, EventInitializerSharesVariable) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* v_done = f.ctx.FindVariable("done");
  auto* v_done_too = f.ctx.FindVariable("done_too");
  ASSERT_NE(v_done, nullptr);
  ASSERT_NE(v_done_too, nullptr);
  EXPECT_EQ(v_done, v_done_too);
}

// §15.5.5: Imperative event assignment shares the Variable object.
TEST(IpcSync, EventImperativeAssignmentSharesVariable) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va, vb);
}

// §15.5.5: Self-assignment of an event is harmless.
TEST(IpcSync, EventSelfAssignment) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    ev = ev;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* v = f.ctx.FindVariable("ev");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// §15.5.5: Event variables act as full-fledged variables with handle semantics.
TEST(IpcSync, EventInitializerPreservesIsEventFlag) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* v = f.ctx.FindVariable("done_too");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// §15.5.5: Chained event assignment shares the same underlying variable.
TEST(IpcSync, ChainedEventAssignmentSharesVariable) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b, c;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    c = a;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va, vb);
  EXPECT_EQ(vc, vb);
}

}  // namespace
