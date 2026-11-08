#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <unordered_set>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameSim, ShallowCopyCopiesRngState) {
  SimFixture f;
  auto* type = MakeClassType(f, "R", {"x"});
  auto [h, obj] = MakeObj(f, type);
  obj->rng_seed = 0xC0FFEEu;
  obj->rng_initialized = true;
  obj->rng.seed(obj->rng_seed);
  (void)obj->rng();
  (void)obj->rng();

  auto* copy = obj->ShallowCopy(f.arena);
  EXPECT_EQ(copy->rng_seed, 0xC0FFEEu);
  EXPECT_TRUE(copy->rng_initialized);
  EXPECT_EQ(copy->rng, obj->rng);
}

TEST(ClassAssignRenameSim, E2eShallowCopyDoesNotRerunFieldInitializer) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x = 7;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, ShallowCopyPreservesDerivedType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"j"});
  auto* ext = MakeClassType(f, "Ext", {"x"});
  ext->parent = base;

  auto [h, obj] = MakeObj(f, ext);
  obj->SetProperty("j", MakeLogic4VecVal(f.arena, 32, 5));
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 9));

  auto* copy = obj->ShallowCopy(f.arena);
  EXPECT_EQ(copy->type, ext);
  EXPECT_EQ(copy->GetProperty("j", f.arena).ToUint64(), 5u);
  EXPECT_EQ(copy->GetProperty("x", f.arena).ToUint64(), 9u);
}

TEST(ClassAssignRenameSim, ShallowCopyGivesEachPropertyItsOwnWords) {
  SimFixture f;
  auto* type = MakeClassType(f, "P", {"lo", "hi"});
  auto [h, obj] = MakeObj(f, type);
  obj->SetProperty("lo", MakeLogic4VecVal(f.arena, 32, 0xDEADBEEFu));
  Logic4Vec hi = MakeLogic4Vec(f.arena, 96);
  hi.words[0].aval = 0x0123456789ABCDEFull;
  hi.words[1].aval = 0x00000000FEEDFACEull;
  hi.words[1].bval = 0x00000000F0000000ull;
  obj->SetProperty("hi", hi);

  auto* copy = obj->ShallowCopy(f.arena);
  ASSERT_EQ(copy->properties.size(), obj->properties.size());
  for (const auto& [name, val] : obj->properties) {
    SCOPED_TRACE(name);
    auto it = copy->properties.find(name);
    ASSERT_NE(it, copy->properties.end());
    ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(val, it->second));
  }
}

TEST(ClassAssignRenameSim, ShallowCopyPropertyDepositLeavesTheSourceIntact) {
  SimFixture f;
  auto* type = MakeClassType(f, "P", {"x"});
  auto [h, obj] = MakeObj(f, type);
  obj->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 0xDEADBEEFu));

  auto* copy = obj->ShallowCopy(f.arena);
  DepositBitField(copy->properties["x"], 0, MakeLogic4VecVal(f.arena, 8, 0), 8);
  EXPECT_EQ(copy->properties["x"].ToUint64(), 0xDEADBE00u);
  EXPECT_EQ(obj->properties["x"].ToUint64(), 0xDEADBEEFu);
}

TEST(ClassAssignRenameSim, E2eHandleAssignmentAliasesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = p1;\n"
      "    p2.x = 42;\n"
      "    result = p1.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesProperties) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C p1, p2;\n"
                      "    p1 = new;\n"
                      "    p1.x = 42;\n"
                      "    p2 = new p1;\n"
                      "    result = p2.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCreatesIndependentObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 10;\n"
      "    p2 = new p1;\n"
      "    p2.x = 99;\n"
      "    r1 = p1.x;\n"
      "    r2 = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 99u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyDoesNotCallConstructor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "    x = 999;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.x = 42;\n"
      "    p2 = new p1;\n"
      "    result = p2.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopySharesNestedHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Inner;\n"
      "  int val;\n"
      "endclass\n"
      "class Outer;\n"
      "  int x;\n"
      "  Inner a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Outer o1, o2;\n"
      "    o1 = new;\n"
      "    o1.a = new;\n"
      "    o1.a.val = 77;\n"
      "    o2 = new o1;\n"
      "    r1 = o2.a.val;\n"
      "    o2.a.val = 88;\n"
      "    r2 = o1.a.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 77u}, {"r2", 88u}});
}

TEST(ClassAssignRenameSim, E2eChainedMemberAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A;\n"
      "  int j;\n"
      "endclass\n"
      "class B;\n"
      "  int i;\n"
      "  A a;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    B b1;\n"
      "    b1 = new;\n"
      "    b1.i = 1;\n"
      "    b1.a = new;\n"
      "    b1.a.j = 50;\n"
      "    r1 = b1.i;\n"
      "    r2 = b1.a.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 50u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyWithInheritance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int j;\n"
      "endclass\n"
      "class Ext extends Base;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Ext e;\n"
      "    Base b;\n"
      "    Base b2;\n"
      "    e = new;\n"
      "    e.j = 5;\n"
      "    e.x = 9;\n"
      "    b = e;\n"
      "    b2 = new b;\n"
      "    r1 = b2.j;\n"
      "    r2 = b.j;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}, {"r2", 5u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyMultipleProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  int c;\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.a = 1;\n"
      "    p1.b = 2;\n"
      "    p1.c = 3;\n"
      "    p2 = new p1;\n"
      "    ra = p2.a;\n"
      "    rb = p2.b;\n"
      "    rc = p2.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 1u}, {"rb", 2u}, {"rc", 3u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesStringProperty) {
  const char* src =
      "class C;\n"
      "  string s;\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int independent;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    p1.s = \"hello\";\n"
      "    p2 = new p1;\n"
      "    copied = (p2.s == \"hello\") ? 1 : 0;\n"
      "    p1.s = \"world\";\n"
      "    independent = (p2.s == \"hello\") ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "copied"), 1u);
  EXPECT_EQ(RunAndGet(src, "independent"), 1u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesRandModeStatus) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int fresh;\n"
      "  initial begin\n"
      "    C p1, p2, p3;\n"
      "    p1 = new;\n"
      "    p1.x.rand_mode(0);\n"
      "    p2 = new p1;\n"
      "    copied = p2.x.rand_mode();\n"
      "    p3 = new;\n"
      "    fresh = p3.x.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "copied"), 0u);
  EXPECT_EQ(RunAndGet(src, "fresh"), 1u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesConstraintModeStatus) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x < 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int copied;\n"
      "  int fresh;\n"
      "  initial begin\n"
      "    C p1, p2, p3;\n"
      "    p1 = new;\n"
      "    p1.c.constraint_mode(0);\n"
      "    p2 = new p1;\n"
      "    copied = p2.c.constraint_mode();\n"
      "    p3 = new;\n"
      "    fresh = p3.c.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "copied"), 0u);
  EXPECT_EQ(RunAndGet(src, "fresh"), 1u);
}

TEST(ClassAssignRenameSim, ShallowCopyCopiesRandcCyclicStateIndependently) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"y"});
  auto [h, obj] = MakeObj(f, type);
  auto history = std::make_shared<std::unordered_set<int64_t>>();
  history->insert(0);
  history->insert(1);
  obj->randc_history["y"] = history;

  auto* copy = obj->ShallowCopy(f.arena);

  ASSERT_TRUE(copy->randc_history.count("y"));
  EXPECT_EQ(copy->randc_history["y"]->size(), 2u);
  EXPECT_TRUE(copy->randc_history["y"]->count(0));
  EXPECT_TRUE(copy->randc_history["y"]->count(1));

  copy->randc_history["y"]->insert(2);
  EXPECT_EQ(obj->randc_history["y"]->size(), 2u);
  EXPECT_FALSE(obj->randc_history["y"]->count(2));
}

TEST(ClassAssignRenameSim, E2eDeclInitShallowCopyCopiesProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c1;\n"
      "    c1 = new;\n"
      "    c1.x = 55;\n"
      "    begin\n"
      "      automatic C c2 = new c1;\n"
      "      result = c2.x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 55u}});
}

TEST(ClassAssignRenameSim, E2eNewThisCopiesTheInvokingObjectsProperties) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new();\n"
                      "    x = 7;\n"
                      "  endfunction\n"
                      "  function int copied_x();\n"
                      "    C copy;\n"
                      "    copy = new this;\n"
                      "    return copy.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C p;\n"
                      "    p = new;\n"
                      "    p.x = 42;\n"
                      "    result = p.copied_x();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassAssignRenameSim, E2eNewThisCopyIsADistinctObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function int copy_and_set();\n"
      "    C copy;\n"
      "    copy = new this;\n"
      "    copy.x = 99;\n"
      "    return copy.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    C p;\n"
      "    p = new;\n"
      "    p.x = 10;\n"
      "    r2 = p.copy_and_set();\n"
      "    r1 = p.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 99u}});
}

TEST(ClassAssignRenameSim, E2eBareThisEvaluatesToTheInvokingObjectHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function C self();\n"
                      "    return this;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C p, q;\n"
                      "    p = new;\n"
                      "    p.x = 55;\n"
                      "    q = p.self();\n"
                      "    result = q.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(ClassAssignRenameSim, E2eDeclInitHandleAssignmentAliasesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C p1;\n"
      "    p1 = new;\n"
      "    p1.x = 33;\n"
      "    begin\n"
      "      automatic C p2 = p1;\n"
      "      p2.x = 77;\n"
      "      result = p1.x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 77u}});
}

TEST(ClassAssignRenameSim, E2eShallowCopyCarriesRandcCyclicState) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b, c, d, distinct;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    ok = p1.randomize();\n"
      "    a = p1.y;\n"
      "    ok = p1.randomize();\n"
      "    b = p1.y;\n"
      "    ok = p1.randomize();\n"
      "    c = p1.y;\n"
      "    p2 = new p1;\n"
      "    ok = p2.randomize();\n"
      "    d = p2.y;\n"
      "    distinct = (d != a && d != b && d != c) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "distinct"), 1u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCarriesRngStream) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, same;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C p1, p2;\n"
      "    p1 = new;\n"
      "    ok = p1.randomize();\n"
      "    p2 = new p1;\n"
      "    ok = p1.randomize();\n"
      "    ok = p2.randomize();\n"
      "    r1 = p1.x;\n"
      "    r2 = p2.x;\n"
      "    same = (r1 == r2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(ClassAssignRenameSim, E2eShallowCopyCopiesQueueProperty) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C a = new;\n"
                      "    C b;\n"
                      "    a.q.push_back(1);\n"
                      "    a.q.push_back(2);\n"
                      "    b = new a;\n"
                      "    b.q.push_back(3);\n"
                      "    out = b.q.size() * 100 + a.q.size() * 10 + b.q[$];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            323u);
}

}  // namespace
