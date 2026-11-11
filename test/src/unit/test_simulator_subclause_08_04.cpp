#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, AllocateNewObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(handle, kNullClassHandle);
  EXPECT_EQ(obj->type, type);
  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 0u);
}

TEST(ClassSim, NewReturnsUniqueHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"x"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  EXPECT_NE(h1, h2);
}

TEST(ClassSim, HandleToObjectLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"val"});
  auto [handle, obj] = MakeObj(f, type);

  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
}

TEST(ClassSim, NullHandleIsZero) { EXPECT_EQ(kNullClassHandle, 0u); }

TEST(ClassSim, GetClassObjectNullReturnsNullptr) {
  SimFixture f;
  auto* obj = f.ctx.GetClassObject(kNullClassHandle);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, GetClassObjectInvalidReturnsNullptr) {
  SimFixture f;
  auto* obj = f.ctx.GetClassObject(99999);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, ClassTypeRegistryLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Registry", {"x"});

  auto* found = f.ctx.FindClassType("Registry");
  EXPECT_EQ(found, type);

  auto* notfound = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(notfound, nullptr);
}

TEST(ClassSim, MultipleObjectsSameType) {
  SimFixture f;
  auto* type = MakeClassType(f, "Widget", {"value"});

  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);

  o1->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 100));
  o2->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 200));

  EXPECT_EQ(o1->GetProperty("value", f.arena).ToUint64(), 100u);
  EXPECT_EQ(o2->GetProperty("value", f.arena).ToUint64(), 200u);
}

TEST(ClassSim, HandleNullAssignment) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

TEST(ClassSim, HandleCaseInequalityDifferentHandlesReturnsOne) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 5);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 6);
  auto result = EvalBinaryOp(TokenKind::kBangEqEq, h1, h2, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleEqualityBothNullReturnsOne) {
  SimFixture f;
  auto null1 = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto null2 = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto result = EvalBinaryOp(TokenKind::kEqEq, null1, null2, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, HandleNotEqualToNullReturnsOne) {
  SimFixture f;
  auto* type = MakeClassType(f, "T", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  auto h = MakeLogic4VecVal(f.arena, 64, handle);
  auto null_h = MakeLogic4VecVal(f.arena, 64, kNullClassHandle);
  auto result = EvalBinaryOp(TokenKind::kBangEq, h, null_h, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ClassSim, CaseEqualitySameSemanticsAsEquality) {
  SimFixture f;
  auto h1 = MakeLogic4VecVal(f.arena, 64, 7);
  auto h2 = MakeLogic4VecVal(f.arena, 64, 7);
  auto h3 = MakeLogic4VecVal(f.arena, 64, 8);
  auto eq = EvalBinaryOp(TokenKind::kEqEq, h1, h2, f.arena);
  auto ceq = EvalBinaryOp(TokenKind::kEqEqEq, h1, h2, f.arena);
  EXPECT_EQ(eq.ToUint64(), ceq.ToUint64());
  auto neq = EvalBinaryOp(TokenKind::kBangEq, h1, h3, f.arena);
  auto cneq = EvalBinaryOp(TokenKind::kBangEqEq, h1, h3, f.arena);
  EXPECT_EQ(neq.ToUint64(), cneq.ToUint64());
}

TEST(ClassSim, IsAReturnsTrueForSameType) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {"x"});
  EXPECT_TRUE(type->IsA(type));
}

TEST(ClassSim, IsAReturnsTrueForParentType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* child = MakeClassType(f, "Child", {"y"});
  child->parent = base;
  EXPECT_TRUE(child->IsA(base));
  EXPECT_FALSE(base->IsA(child));
}

TEST(ClassSim, IsAReturnsFalseForUnrelatedType) {
  SimFixture f;
  auto* a = MakeClassType(f, "A", {"x"});
  auto* b = MakeClassType(f, "B", {"y"});
  EXPECT_FALSE(a->IsA(b));
  EXPECT_FALSE(b->IsA(a));
}

TEST(ClassSim, AssignedHandlesAliasSameObjectCompareEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic eq;\n"
      "  logic ceq;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = a;\n"
      "    eq = (a == b);\n"
      "    ceq = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* eq = f.ctx.FindVariable("eq");
  auto* ceq = f.ctx.FindVariable("ceq");
  ASSERT_NE(eq, nullptr);
  ASSERT_NE(ceq, nullptr);
  EXPECT_EQ(eq->value.ToUint64(), 1u);
  EXPECT_EQ(ceq->value.ToUint64(), 1u);
}

TEST(ClassSim, DistinctObjectsCompareUnequal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic eq;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    eq = (a == b);\n"
      "    neq = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* eq = f.ctx.FindVariable("eq");
  auto* neq = f.ctx.FindVariable("neq");
  ASSERT_NE(eq, nullptr);
  ASSERT_NE(neq, nullptr);
  EXPECT_EQ(eq->value.ToUint64(), 0u);
  EXPECT_EQ(neq->value.ToUint64(), 1u);
}

TEST(ClassSim, ConditionalOperatorSelectsHandleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  logic picks_a;\n"
      "  logic picks_b;\n"
      "  initial begin\n"
      "    C a, b, ta, tb;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    ta = 1'b1 ? a : b;\n"
      "    tb = 1'b0 ? a : b;\n"
      "    picks_a = (ta == a);\n"
      "    picks_b = (tb == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* pa = f.ctx.FindVariable("picks_a");
  auto* pb = f.ctx.FindVariable("picks_b");
  ASSERT_NE(pa, nullptr);
  ASSERT_NE(pb, nullptr);
  EXPECT_EQ(pa->value.ToUint64(), 1u);
  EXPECT_EQ(pb->value.ToUint64(), 1u);
}

TEST(ClassSim, CompatibleDerivedHandleAssignmentAliasesAtRuntime) {
  SimFixture f;
  auto* aliased = RunAndFindVar(
      "class Base; endclass\n"
      "class Child extends Base; endclass\n"
      "module m;\n"
      "  logic aliased;\n"
      "  initial begin\n"
      "    Base bh;\n"
      "    Child ch;\n"
      "    ch = new;\n"
      "    bh = ch;\n"
      "    aliased = (bh == ch);\n"
      "  end\n"
      "endmodule\n",
      f, "aliased");
  ASSERT_NE(aliased, nullptr);
  EXPECT_EQ(aliased->value.ToUint64(), 1u);
}

TEST(ClassSim, NullAssignmentClearsHandleAtRuntime) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "class C; endclass\n"
      "module m;\n"
      "  logic is_null;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    h = null;\n"
      "    is_null = (h == null);\n"
      "  end\n"
      "endmodule\n",
      f, "is_null");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(ClassSim, UninitializedHandleDetectableAsNull) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module m;\n"
      "  C h;\n"
      "  logic is_null;\n"
      "  initial is_null = (h == null);\n"
      "endmodule\n",
      f, "is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ClassSim, NewConstructsHandleDeclaredInFunctionBody) {
  const char* src =
      "class P;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int f();\n"
      "    P p;\n"
      "    p = new;\n"
      "    return (p == null) ? 111 : 222;\n"
      "  endfunction\n"
      "  initial rx = f();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 222u);
}

TEST(ClassSim, NewInitializerConstructsHandleDeclaredInFunctionBody) {
  const char* src =
      "class P;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int f();\n"
      "    static P p = new;\n"
      "    return (p == null) ? 111 : 222;\n"
      "  endfunction\n"
      "  initial rx = f();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 222u);
}

TEST(ClassSim, PropertyOfHandleConstructedInFunctionBodyReadsBack) {
  const char* src =
      "class P;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int f();\n"
      "    P p;\n"
      "    p = new;\n"
      "    p.x = 42;\n"
      "    return p.x;\n"
      "  endfunction\n"
      "  initial rx = f();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ClassSim, NewConstructsHandleDeclaredInClassMethodBody) {
  const char* src =
      "class Q;\n"
      "  int x;\n"
      "endclass\n"
      "class P;\n"
      "  function int mk();\n"
      "    Q q;\n"
      "    q = new;\n"
      "    return (q == null) ? 111 : 222;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    rx = p.mk();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 222u);
}

TEST(ClassSim, MethodCalledThroughANullHandleIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int v = 5;\n"
      "  function int get();\n"
      "    return v;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r = 99;\n"
      "  C c;\n"
      "  initial r = c.get();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' called through the null handle 'c'",
                            10, "8.4"));
}

TEST(ClassSim, StaticMethodCalledThroughANullHandleRuns) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  static function int seven();\n"
      "    return 7;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int r = 99;\n"
      "  C c;\n"
      "  initial r = c.seven();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 7u);
}

const char* const kNullReceiverClasses =
    "class C;\n"
    "  int v = 5;\n"
    "  function int get(); return v; endfunction\n"
    "  task put(); v = 9; endtask\n"
    "  static function int seven(); return 7; endfunction\n"
    "endclass\n"
    "class H;\n"
    "  C inner;\n"
    "endclass\n";

static int CountReports(const SimFixture& f, std::string_view text) {
  int n = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find(text) != std::string::npos) ++n;
  }
  return n;
}

TEST(ClassSim, MethodCalledThroughANullArrayElementIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  int r = 99;\n"
                                  "  C arr[1];\n"
                                  "  initial r = arr[0].get();\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' called through a null handle", 13,
                            "8.4"));
}

TEST(ClassSim, TaskEnabledThroughANullHeldHandleIsReportedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  H h;\n"
                                  "  initial begin\n"
                                  "    h = new;\n"
                                  "    h.inner.put();\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' called through a null handle", 14,
                            "8.4"));
  EXPECT_EQ(CountReports(f, "called through a null handle"), 1);
}

TEST(ClassSim, TaskEnabledThroughANamedNullHandleIsReportedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  C n;\n"
                                  "  initial n.put();\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' called through the null handle 'n'",
                            12, "8.4"));
  EXPECT_EQ(CountReports(f, "called through the null handle"), 1);
}

TEST(ClassSim, MethodCalledThroughANullReturnedHandleIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  int r = 99;\n"
                                  "  function automatic C none();\n"
                                  "    return null;\n"
                                  "  endfunction\n"
                                  "  initial r = none().get();\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' called through a null handle", 15,
                            "8.4"));
}

TEST(ClassSim, MethodCalledThroughANullAssociativeEntryIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  int r = 99;\n"
                                  "  C aa[string];\n"
                                  "  initial begin\n"
                                  "    aa[\"k\"] = null;\n"
                                  "    r = aa[\"k\"].get();\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' called through a null handle", 15,
                            "8.4"));
  EXPECT_EQ(CountReports(f, "called through a null handle"), 1);
}

TEST(ClassSim, StaticMethodCalledThroughANullAssociativeEntryRuns) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  int r = 99;\n"
                                  "  C aa[string];\n"
                                  "  initial begin\n"
                                  "    aa[\"k\"] = null;\n"
                                  "    r = aa[\"k\"].seven();\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 7u);
}

TEST(ClassSim, StaticMethodCalledThroughANullArrayElementRuns) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string(kNullReceiverClasses) +
                                  "module m;\n"
                                  "  int r = 99;\n"
                                  "  C arr[1];\n"
                                  "  initial r = arr[0].seven();\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 7u);
}

static std::pair<uint64_t, uint64_t> RunAndReadValueAndBits(
    const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  if (design == nullptr) return {0, 0};
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  auto* w = f.ctx.FindVariable("w");
  EXPECT_NE(r, nullptr);
  EXPECT_NE(w, nullptr);
  if (r == nullptr || w == nullptr) return {0, 0};
  return {r->value.ToUint64(), w->value.ToUint64()};
}

TEST(ClassSim, CompilationUnitLocalparamSizesClassPropertyRange) {
  auto [r, w] = RunAndReadValueAndBits(
      "localparam int W = 10;\n"
      "class C;\n"
      "  logic [W-1:0] v;\n"
      "endclass\n"
      "module t;\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

TEST(ClassSim, PackageParameterSizesClassPropertyRange) {
  auto [r, w] = RunAndReadValueAndBits(
      "package p;\n"
      "  parameter int W = 10;\n"
      "endpackage\n"
      "class C;\n"
      "  logic [p::W-1:0] v;\n"
      "  logic [p::W*2-1:0] u;\n"
      "endclass\n"
      "module t;\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    c.u = 20'hFFFFF;\n"
      "    r = c.u;\n"
      "    w = $bits(c.v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1048575u);
  EXPECT_EQ(w, 10u);
}

TEST(ClassSim, ImportedPackageParameterSizesClassPropertyRange) {
  auto [r, w] = RunAndReadValueAndBits(
      "package p;\n"
      "  parameter int W = 10;\n"
      "endpackage\n"
      "import p::*;\n"
      "class C;\n"
      "  logic [W-1:0] v;\n"
      "  logic [p::W-1:0] u;\n"
      "endclass\n"
      "module t;\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

TEST(ClassSim, ClassDeclaredInModuleSizesPropertyByUnitConstants) {
  auto [r, w] = RunAndReadValueAndBits(
      "package p;\n"
      "  parameter int W = 10;\n"
      "endpackage\n"
      "localparam int K = 10;\n"
      "module t;\n"
      "  class C;\n"
      "    logic [p::W-1:0] v;\n"
      "    logic [K-1:0] u;\n"
      "  endclass\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

static std::string HandleArrayDesign(std::string_view rest) {
  return "class C;\n"
         "  int v = 7;\n"
         "endclass\n" +
         std::string(rest);
}

TEST(ClassSim, NewIntoAnElementOfADeclaredFixedArrayIsReadThroughIt) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  C arr[2];\n"
                                        "  int y;\n"
                                        "  initial begin\n"
                                        "    arr[0] = new;\n"
                                        "    y = arr[0].v;\n"
                                        "  end\n"
                                        "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassSim, NewIntoAnElementOfADeclaredDynamicArrayIsReadThroughIt) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  C d[];\n"
                                        "  int y;\n"
                                        "  initial begin\n"
                                        "    d = new[2];\n"
                                        "    d[1] = new;\n"
                                        "    y = d[1].v;\n"
                                        "  end\n"
                                        "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassSim, NewIntoElementsOfBlockDeclaredArraysIsReadThroughThem) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  int y;\n"
                                        "  initial begin\n"
                                        "    C arr[2];\n"
                                        "    C d[];\n"
                                        "    arr[1] = new;\n"
                                        "    d = new[2];\n"
                                        "    d[0] = new;\n"
                                        "    y = arr[1].v * 10 + d[0].v;\n"
                                        "  end\n"
                                        "endmodule\n"),
                      "y"),
            77u);
}

TEST(ClassSim, NewIntoAnElementOfAFunctionBodyArrayIsReadThroughIt) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  function int f();\n"
                                        "    C arr[2];\n"
                                        "    arr[0] = new;\n"
                                        "    return arr[0].v;\n"
                                        "  endfunction\n"
                                        "  int y;\n"
                                        "  initial y = f();\n"
                                        "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassSim, NewIntoAnElementOfATaskBodyDynamicArrayIsReadThroughIt) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  int y;\n"
                                        "  task build();\n"
                                        "    C d[];\n"
                                        "    d = new[2];\n"
                                        "    d[1] = new;\n"
                                        "    y = d[1].v;\n"
                                        "  endtask\n"
                                        "  initial build();\n"
                                        "endmodule\n"),
                      "y"),
            7u);
}

TEST(ClassSim, NewIntoAHandlePropertyOfADeclaredArrayElementConstructsIt) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int v = 9;\n"
                      "endclass\n"
                      "class C;\n"
                      "  N h;\n"
                      "endclass\n"
                      "module t;\n"
                      "  C arr[2];\n"
                      "  N n;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    arr[1] = new;\n"
                      "    arr[1].h = new;\n"
                      "    n = arr[1].h;\n"
                      "    y = n.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            9u);
}

TEST(ClassSim, AWriteThroughAVariableIndexedElementReachesItsObject) {
  EXPECT_EQ(RunAndGet(HandleArrayDesign("module t;\n"
                                        "  C arr[2];\n"
                                        "  int i = 1;\n"
                                        "  int y;\n"
                                        "  initial begin\n"
                                        "    arr[1] = new;\n"
                                        "    arr[i].v = 5;\n"
                                        "    y = arr[1].v;\n"
                                        "  end\n"
                                        "endmodule\n"),
                      "y"),
            5u);
}

TEST(ClassSim, NewThroughAVariableIndexedElementIsStoredInItsObject) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int v = 9;\n"
                      "endclass\n"
                      "class C;\n"
                      "  N h;\n"
                      "endclass\n"
                      "module t;\n"
                      "  C arr[2];\n"
                      "  N n;\n"
                      "  int i = 1;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    arr[1] = new;\n"
                      "    arr[i].h = new;\n"
                      "    n = arr[1].h;\n"
                      "    y = n.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            9u);
}

TEST(ClassSim, VirtualMethodsCalledThroughANullHandleAreReportedAndRunGoesOn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class B;\n"
      "  virtual function int vf(); return 1; endfunction\n"
      "  virtual task vt(); endtask\n"
      "endclass\n"
      "class D extends B;\n"
      "  virtual function int vf(); return 2; endfunction\n"
      "endclass\n"
      "virtual class A; pure virtual function int pf(); endclass\n"
      "interface class I; pure virtual function int itf(); endclass\n"
      "module m;\n"
      "  int r, done;\n"
      "  B c, b; A a; I ii;\n"
      "  initial begin\n"
      "    r = c.vf();\n"
      "    c.vt();\n"
      "    r = b.vf();\n"
      "    r = a.pf();\n"
      "    r = ii.itf();\n"
      "    done = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const struct {
    uint32_t line;
    const char* message;
  } kReports[] = {
      {14, "method 'vf' called through the null handle 'c'"},
      {15, "method 'vt' called through the null handle 'c'"},
      {16, "method 'vf' called through the null handle 'b'"},
      {17, "method 'pf' called through the null handle 'a'"},
      {18, "method 'itf' called through the null handle 'ii'"},
  };
  for (const auto& report : kReports) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), report.message, report.line, "8.4"))
        << report.line;
  }
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
}

TEST(ClassSim, PropertyReachedThroughANullHandleLetsRunGoOnAndChangesNoObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int v = 5;\n"
      "endclass\n"
      "class O;\n"
      "  O peer;\n"
      "  int v = 4;\n"
      "  function int rd(); return peer.v; endfunction\n"
      "  function void wr(); peer.v = 6; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c, d;\n"
      "  O o;\n"
      "  int r, a1, a2, a3, a4, w1, w2, w3, w4, rc, rd2, ro;\n"
      "  task t(); r = c.v; a2 = 1; c.v = 2; w2 = 1; endtask\n"
      "  function void f(); r = c.v; a3 = 1; c.v = 3; w3 = 1; endfunction\n"
      "  initial begin\n"
      "    d = new;\n"
      "    r = c.v;\n"
      "    a1 = 1;\n"
      "    c.v = 1;\n"
      "    w1 = 1;\n"
      "    t();\n"
      "    f();\n"
      "    o = new;\n"
      "    r = o.rd();\n"
      "    a4 = 1;\n"
      "    o.wr();\n"
      "    w4 = 1;\n"
      "    rd2 = d.v;\n"
      "    ro = o.v;\n"
      "    c = new;\n"
      "    rc = c.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (const char* name : {"a1", "a2", "a3", "a4", "w1", "w2", "w3", "w4"}) {
    EXPECT_EQ(f.ctx.FindVariable(name)->value.ToUint64(), 1u) << name;
  }
  EXPECT_EQ(f.ctx.FindVariable("rc")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("rd2")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("ro")->value.ToUint64(), 4u);
}

}  // namespace
