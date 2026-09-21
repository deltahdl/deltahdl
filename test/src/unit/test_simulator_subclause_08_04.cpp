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

// §8.4: assignment of a class object copies the handle, so two variables that
// were assigned from the same allocated object refer to that one object and
// compare equal. Exercised end to end (elaborate/lower/run) rather than from a
// hand-built handle value: 'new' produces the object, the assignment aliases
// the second handle, and the listed '==' / '===' operators observe the alias.
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

// §8.4: distinct objects created by separate 'new' calls have distinct handles,
// so handles pointing at different objects compare unequal. Built from real
// source syntax and run through the full pipeline so the '==' / '!=' operators
// act on handles the allocator actually produced.
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

// §8.4: the conditional operator is one of the operators valid on object
// handles. Built end to end from 11.4.11's real ternary syntax -- two distinct
// objects are allocated and each branch is selected in turn, so the result
// handle aliases the object the condition chose, observed with '=='.
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

// §8.4: assignment of a class object whose type is assignment compatible with
// the target is valid. The compatible source is a derived-class handle built
// from 6.22.3's real 'extends' inheritance; after assigning it into a base
// handle the two handles alias the one object, observed with '=='.
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

// §8.4: assignment of null is a valid operation on an object handle. After an
// object is allocated and null is then assigned over it, comparing the handle
// with null yields true -- observed end to end rather than from a hand-set
// handle value.
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

// 8.4: an object "is used by first declaring a variable of that class type
// (that holds an object handle) and then creating an object of that class
// (using the new function) and assigning it to the variable" -- the clause
// illustrates it with `Packet p; p = new;`. Nothing there makes the
// construction depend on the construct the declaration sits in, so a handle
// local to a function body is constructed exactly as one in an initial block
// is. The handle is compared against null rather than a property being read,
// so the test reports whether an object exists rather than what it contains.
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

// 8.4, the declaration-initializer spelling of the same construction: the
// object is created where the handle is declared rather than by a later
// assignment, and a function body is no exception.
TEST(ClassSim, NewInitializerConstructsHandleDeclaredInFunctionBody) {
  const char* src =
      "class P;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int f();\n"
      "    P p = new;\n"
      "    return (p == null) ? 111 : 222;\n"
      "  endfunction\n"
      "  initial rx = f();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 222u);
}

// 8.4: the object a function-body handle refers to is a whole object, so its
// properties are writable and read back. Constructing the handle is not enough
// on its own -- a handle left null would read 0 here for the same reason it
// would report null above, so this pins the object down as usable rather than
// merely non-null.
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

// 8.4: a class method's body is a subroutine body like any other, so a handle
// local to a method is constructed there too.
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
      "    P p = new;\n"
      "    rx = p.mk();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 222u);
}

// §8.4 (printed page 182 of IEEE 1800-2023): accessing a non-static
// member or a virtual method through a null object handle is illegal, the
// result indeterminate, and an implementation may issue an error. `c.get()` on
// a `C c;` never assigned answered 0 in silence, a value a testbench reads as
// valid; it is reported at the call, and the 0 is what the call yields.
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

// §8.10: a static method belongs to the class and is callable through a
// handle whether or not it refers to an object, so the null handle raises no
// report and the method runs.
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

// Elaborates, lowers and runs `src` clean, then reads the value the run left
// in `r` and the width `$bits` reported into `w`. A property that folded to
// its base type's one bit truncates the value written through it and reports
// that one bit, so both are what the sizing of the property decides.
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

// §6.20.4 (printed page 129 of IEEE 1800-2023) lets a local parameter be
// declared at compilation-unit scope, §3.12.1 (printed 56) has a name the class
// body does not declare searched in the compilation-unit scope written before
// it, and §7.4.1 (printed 153) has a packed dimension's bounds be constant
// expressions. The property is therefore ten bits: 10'h3FF written through it
// reads back 1023 and $bits answers 10. Folded against the class's own
// parameters alone, the range did not fold, the property was the one bit of
// its `logic` base type, and both read 1.
TEST(ClassSim, CompilationUnitLocalparamSizesClassPropertyRange) {
  auto [r, w] = RunAndReadValueAndBits(
      "localparam int W = 10;\n"
      "class C;\n"
      "  logic [W-1:0] v;\n"
      "endclass\n"
      "module t;\n"
      "  int r, w;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

// §26.3 (printed page 808 of IEEE 1800-2023): a package's parameter is
// named from any scope through the package scope resolution operator, and
// §7.4.1 admits any constant expression as a bound, so `[p::W*2-1:0]` is twenty
// bits where
// `[p::W-1:0]` is ten. 20'hFFFFF reads back 1048575 from the doubled range,
// which a ten-bit property would have cut to 1023 and a one-bit one to 1.
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
      "    C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    c.u = 20'hFFFFF;\n"
      "    r = c.u;\n"
      "    w = $bits(c.v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1048575u);
  EXPECT_EQ(w, 10u);
}

// §3.12.1 (printed page 56 of IEEE 1800-2023) includes among the
// compilation-unit scope's names the ones a package import made available
// there, so a wildcard import written outside every module lets the class body
// name the package's parameter bare. The bare and the qualified spellings size
// alike: 10'h3FF through the bare-named range reads 1023 and $bits of the
// qualified one is 10.
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
      "    C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

// §8.26 lets a class declaration stand within a module, and §3.12.1's search
// reaches the compilation-unit scope from there as from a class declared in
// it, so a module's class sizes its properties by the unit's localparam and
// by a package's parameter as a compilation-unit class does: 10'h3FF through
// the package-sized property reads 1023 and the localparam-sized one is ten
// bits wide.
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
      "    C c = new;\n"
      "    c.v = 10'h3FF;\n"
      "    r = c.v;\n"
      "    w = $bits(c.u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r, 1023u);
  EXPECT_EQ(w, 10u);
}

// §8.4 (printed page 181 of the LRM): a variable of a class type holds an
// object handle, and §7.4.2 (printed 153-154) and §7.5 (printed 157) make
// each element of an unpacked array a variable of the element type, so
// `C arr[2]` is two handles, each constructed by `new` into its element and
// read through it. The three tests below share the class and read 7, its
// property's initializer; a `new` that constructed nothing and a read that
// reached no object answer 0.
static std::string HandleArrayDesign(std::string_view rest) {
  return "class C;\n"
         "  int v = 7;\n"
         "endclass\n" +
         std::string(rest);
}

// The module-scope fixed-size array: `arr[0] = new` had no path (the `new`
// target key named no select, and the element constructors served array
// properties alone) and `arr[0].v` none either, the member name built from
// the select being no variable's.
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

// The module-scope dynamic array, sized by new[] (§7.5.1) and then given an
// object in its second element.
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

// Both arrays declared in the initial block itself, whose elements are the
// block's own (§7.4.2 in a begin-end block): 77 is the fixed array's second
// element then the dynamic array's first.
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

// §13.4 (printed page 340): a function body's declarations are the body's
// own, and §7.4.2 (printed 153-154) with §8.4 (printed 181) make each element
// of the body's `C arr[2]` a handle. The body's assignment reaches the
// element constructor through the module path's dispatch
// (TryDispatchSpecialBlockingAssign, which ExecFuncBlockingAssign in
// eval_function_body_assign.cpp asks after its own four forms), so `arr[0] =
// new` constructs into the local's element and `arr[0].v` reads its 7. Pinned
// here for the subroutine-body shape, beside the block's.
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

// The same statement in a task body, whose dynamic local is sized by new[]
// first (§7.5.1, printed 158) and written to the module's y.
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

}  // namespace
