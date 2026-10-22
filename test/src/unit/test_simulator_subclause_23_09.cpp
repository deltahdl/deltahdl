// §23.9 "Scope rules" lists Modules first among the elements that define a new
// scope, and fixes where a direct (non-hierarchical) reference is allowed to
// look: a local declaration is used if there is one, and otherwise the search
// climbs until it finds an item of that name or reaches the edge of a module,
// interface, program or checker, a search for a variable stopping at the
// module's edge. Example 1 restates the limit for Figure 23-2: the upward
// search reaches every enclosing rectangle, the module A's edge being the
// farthest.
//
// This file covers that rule for the identifiers inside a *declaration
// initializer* of a variable declared in an instantiated module: `int q = P;`
// in a child must read the child instance's own `P`, and `logic [7:0] b = a;`
// must read the child's own `a` whether or not the top declares one.
//
// The ten UpwardNameReferenceSimulation cases in
// test/src/unit/test_simulator_subclause_23_08.cpp resolve names from inside an
// `initial` block of an instantiated module. A procedural read runs with
// SimContext::current_process_ set to a Process carrying its instance prefix,
// so those cases exercise a resolution path that already takes the instance
// into account and say nothing about the declaration-initializer path, where
// the initializer is evaluated during lowering with no process running. Every
// case here therefore declares the initializer in the child's body and reads
// the result back through the instance prefix, without an `initial` block on
// the child side.
//
// The last four cases cover the other half of the same rule, and reach the
// resolution directly rather than through an initializer: each lowers a design,
// puts an instance prefix in force with SimContext::SetLoweringInstancePrefix,
// and asks SimContext::FindVariable for a name the child does not declare.
//
// Every case holds distinct nonzero values on the two sides of the module
// boundary, because .claude/memories/discriminating-test-inputs.md rules that
// an input that cannot fail proves nothing: a child and a top holding the same
// value -- or a pair of 4-state variables both left at x -- yield the answer
// §23.9 requires even when the initializer read the wrong scope.

#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A parameter is the item §23.9 protects most sharply, because a parameter is
// instance-specific: `child #(.P(7)) u1();` gives u1 its own P, and the local
// P is what the rule that a local declaration is the one used picks out. No
// existing case initializes a child's variable from that child's own parameter;
// UpwardParameterReferenceSimulation reads `parent.P` by hierarchical path from
// an `initial` block, which is neither a direct reference nor a declaration
// initializer.
TEST(InstanceScopeSimulation, ChildInitializerReadsOwnInstanceParameter) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

// The consequence §23.9 forces and no other case observes: two instances of one
// module must initialize from their own overrides, so u1.q and u2.q must
// differ. A single-instance case cannot catch a resolution that ignores the
// instance entirely, because with one instance there is only one answer to
// give; this one fails whenever both copies are initialized from the same
// scope, whatever value that scope holds.
TEST(InstanceScopeSimulation,
     TwoInstancesInitializeFromTheirOwnParameterOverride) {
  SimFixture f;
  auto* q1 = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "  child #(.P(9)) u2();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q1, nullptr);
  auto* q2 = f.ctx.FindVariable("u2.q");
  ASSERT_NE(q2, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 7u);
  EXPECT_EQ(q2->value.ToUint64(), 9u);
}

// A local declaration is the one used -- the child declares its own `a`, so the
// search must not leave the child at all, even though the top declares a
// variable of the same name that is already initialized by the time the child's
// declarations are lowered. 0xA5 and 0x3C share no bits that would let a wrong
// read pass, and both are nonzero so neither can be confused with an unresolved
// identifier's zero.
TEST(InstanceScopeSimulation,
     ChildInitializerPrefersOwnDeclarationOverTopSameName) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a = 8'h3C;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

// The same child under a top that declares no `a` at all. This separates the
// two ways the rule can be broken, which the case above cannot tell apart: a
// search that walks past the module boundary lands on the top's `a` when the
// top has one, and on nothing when it does not. Only the absent-declaration
// form shows that the child's own `a` was never consulted, since the answer
// then is neither of the two declared values.
TEST(InstanceScopeSimulation,
     ChildInitializerWithNoTopDeclarationReadsOwnVariable) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

// An event initializer names the aliased event by a direct reference, so §23.9
// governs it exactly as it governs a value initializer, and the alias is
// observable as pointer identity rather than as a number. No existing case
// aliases an event inside an instance:
// Simulator.EventAliasInitializerSharesSyncObject in
// test/src/unit/test_simulator_subclause_06_17.cpp declares both events in the
// top module, where there is no boundary to cross. The top's own `e1` is the
// wrong target this case rules out, and pointer identity distinguishes it from
// the child's `e1` however either event behaves at run time.
TEST(InstanceScopeSimulation, ChildEventInitializerAliasesOwnInstanceEvent) {
  SimFixture f;
  auto* e2 = RunAndFindVar(
      "module child;\n"
      "  event e1;\n"
      "  event e2 = e1;\n"
      "endmodule\n"
      "module top;\n"
      "  event e1;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.e2");
  ASSERT_NE(e2, nullptr);
  auto* e1 = f.ctx.FindVariable("u1.e1");
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e2, e1);
}

// `new[n](src)` names its source array by a direct reference too, and a dynamic
// array is stored as a queue rather than as a Variable, so it is resolved by a
// different lookup than every case above.
// DynamicArrayNewSimulation.DeclNewWithInitCopiesElements in
// test/src/unit/test_simulator_subclause_07_05_01.cpp declares both arrays in
// the top module, so no case reaches the copy source across a module boundary.
// The two source arrays hold disjoint nonzero elements, so element 0 alone says
// which array was copied.
TEST(InstanceScopeSimulation, ChildDynArrayNewCopiesFromOwnInstanceSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int src[] = '{4, 5};\n"
      "  int dst[] = new[2](src);\n"
      "endmodule\n"
      "module top;\n"
      "  int src[] = '{1, 2};\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* dst = f.ctx.FindQueue("u1.dst");
  ASSERT_NE(dst, nullptr);
  ASSERT_FALSE(dst->elements.empty());
  EXPECT_EQ(dst->elements[0].ToUint64(), 4u);
}

// §23.9 stops the upward search for a variable at the enclosing module: the
// search climbs until it finds an item of that name or reaches the edge of a
// module, interface, program or checker, and a search for a variable stops at
// the module's edge. `v` is declared in `top` alone, so from inside instance
// `u1` the bare name `v` names nothing and must resolve to nothing. The six
// cases above cannot catch this, because each one declares the name it reads in
// the child, so each resolves at the prefixed key and never reaches the
// bare-name lookup this case is about.
TEST(InstanceScopeSimulation,
     BareNameDoesNotReachTopVariableFromInsideInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // Lowering restores the prefix to empty when it finishes, so the instance the
  // reference sits in is stated here.
  f.ctx.SetLoweringInstancePrefix("u1.");
  EXPECT_EQ(f.ctx.FindVariable("v"), nullptr);
}

// §23.9: a local declaration is the one used. `q` is declared in the child, so
// under prefix `u1.` it must still resolve, and to the child's own copy holding
// 7. This case exists to constrain the fix rather than to catch the defect: it
// passes today, and it is what fails if the bare name is stopped by narrowing
// the *prefixed* lookup instead of the bare one. Do not delete it as redundant
// with the case above -- that case alone is satisfied by a resolution that
// finds nothing at all.
TEST(InstanceScopeSimulation, LocalNameStillResolvesUnderInstancePrefix) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

// §23.8 "Upwards name referencing" permits by hierarchical path exactly what
// §23.9 denies to a direct reference: a lower-level module may refer to items
// of a module above it, and to variables when it knows that module's name or
// instance name. Syntax 23-8 gives the form as `module_identifier . item_name`,
// with variable_identifier among the item names, so `top.v` must still resolve
// to the top's `v` holding 3 from inside `u1`. This case exists to constrain
// the fix rather than to catch the defect: it passes today, and it is what
// fails if the upward reach is removed outright instead of being restricted to
// the dotted form. Do not delete it as redundant with the §23.8 cases in
// test/src/unit/test_simulator_subclause_23_08.cpp -- every one of those runs
// inside an `initial` block, where the prefix comes from the running process,
// so none covers the dotted climb under a lowering prefix. `top` is the name
// the design root is registered under: Lowerer::LowerModule registers the top
// module's own name against the empty instance key, and
// FindVariableByPrefixWalk strips the leading `top` segment against that key to
// reach the unprefixed `v`.
TEST(InstanceScopeSimulation, HierarchicalNameStillClimbsPastModuleBoundary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  auto* v = f.ctx.FindVariable("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 3u);
}

// §6.20 makes `P` a constant and not a variable: a constant is a named data
// object that never changes, and parameter, localparam and specparam are the
// three elaboration-time constants. So the variable-specific sentence of §23.9
// does not name it, and this case rests on the general one above that sentence:
// the search climbs until it finds an item of that name or reaches the edge of
// a module, interface, program or checker. A parameter is none of the task,
// function, named block or generate block that sentence lets past a module
// boundary, so a bare `P` inside `u1` must resolve to nothing even though the
// top declares one. This catches what the case above it cannot: a parameter is
// lowered by Lowerer::LowerParams rather than as a module variable, so a fix
// that stops the boundary crossing for one need not stop it for the other. The
// two parameter cases at the top of this file read the child's own `P`, which
// resolves at the prefixed key.
TEST(InstanceScopeSimulation, BareParameterNameDoesNotReachTopParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int P = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  EXPECT_EQ(f.ctx.FindVariable("P"), nullptr);
}

// §23.9 makes a begin-end block a scope and a declaration inside it local to
// that block, so the shape of an array declared there stands for that array
// only while the block is running. SimContext::array_infos_ is flat and nothing
// clears it, so the shape used to answer for a like-named variable afterwards:
// EvalSelect tries an array element select ahead of the packed bit-select, and
// element 1 of an array whose element variables went away with their scope
// reads x rather than bit 1 of the module's own `a`.
//
// The read stands after the block, because one taken inside it reads the
// block's array whether the registration is scoped or not. 8'b1010_1010 has bit
// 1 set, so the assertion tells a bit-select from an x.
TEST(InstanceScopeSimulation, BlockLocalArrayShapeDoesNotOutliveItsBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic got;\n"
      "  initial begin\n"
      "    a = 8'b1010_1010;\n"
      "    begin\n"
      "      int a [1:2];\n"
      "      a[1] = 5;\n"
      "    end\n"
      "    got = a[1];\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §13.4 gives a formal argument the lifetime of the call, so an array formal's
// shape goes away when the call returns, as the per-element formal variables
// bound with it already do. The call is made rather than merely declared: one
// that never runs binds nothing and cannot fail.
TEST(InstanceScopeSimulation, ArrayFormalShapeDoesNotOutliveTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic got;\n"
      "  int src [1:2];\n"
      "  function int take(input int a [1:2]);\n"
      "    return a[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 8'b1010_1010;\n"
      "    src[1] = 4; src[2] = 5;\n"
      "    got = take(src);\n"
      "    got = a[1];\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §23.9 (printed page 761): a name referenced directly within a function is
// declared in the function or in a scope higher in the same branch of the
// name tree, so the search climbs from the body outward through the module
// declaring it, and the body of the caller, which is another branch, is
// never searched. read_n's bare n is the module's 7 while caller() holds a
// local n of 3. The search walked every frame on the stack, the caller's
// included, so read_n read the caller's 3.
TEST(InstanceScopeSimulation, FunctionBareNameDoesNotReachItsCallersLocal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int n = 7;\n"
                      "  int result;\n"
                      "  function automatic int read_n();\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "  function automatic int caller();\n"
                      "    int n = 3;\n"
                      "    return read_n();\n"
                      "  endfunction\n"
                      "  initial result = caller();\n"
                      "endmodule\n",
                      "result"),
            7u);
}

// The same rule for a static method (§8.10) naming the class's static
// property bare, which is uvm_coreservice_t's `inst` under a caller holding
// a local of that name: C::set(c) from first(), whose local `C inst` is not
// in the method's scope, stores c in C's own inst, so C::get() reads c's k
// of 4 from first() and again from second(), 44. Resolved against the
// caller's frame, set wrote first's local and get read it there, 4, then
// read the class's untouched null from second, 1, for 41 -- and
// uvm_coreservice_t::get() found its inst null on every later call and
// re-entered uvm_init without end.
TEST(InstanceScopeSimulation, StaticMethodBareStaticIsNotItsCallersLocal) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static C inst;\n"
                      "  int k = 4;\n"
                      "  static function void set(C c); inst = c; endfunction\n"
                      "  static function C get(); return inst; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  function automatic int first();\n"
                      "    C inst;\n"
                      "    C c = new;\n"
                      "    C::set(c);\n"
                      "    return C::get() == null ? 1 : C::get().k;\n"
                      "  endfunction\n"
                      "  function automatic int second();\n"
                      "    return C::get() == null ? 1 : C::get().k;\n"
                      "  endfunction\n"
                      "  initial result = first() * 10 + second();\n"
                      "endmodule\n",
                      "result"),
            44u);
}

// §23.9: a name a procedural assignment writes is looked up from the
// procedure outward to the module's edge, and one declared nowhere on that
// path is reported. The run writes nothing for it and goes on, so the
// statement after it still sets done.
TEST(InstanceScopeSimulation, AnAssignmentToANameDeclaredNowhereIsSkipped) {
  SimFixture f;
  auto* done = RunAndFindVar(
      "module t;\n"
      "  int done = 0;\n"
      "  initial begin\n"
      "    nosuch = 1;\n"
      "    done = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "done");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'nosuch'", 4, "23.9"));
  ASSERT_NE(done, nullptr);
  EXPECT_EQ(done->value.ToUint64(), 1u);
}

// §23.9 has a class open a scope, and a name written in it find the class's own
// declaration before any outside it, so a structure typedef the class declares
// lays out a member written `nib_t` by the class's 4-bit nib_t: S is 5 bits,
// and 9'h1F5 keeps its low five, x reading 10 and y 1. Laid out by the
// compilation unit's 8-bit nib_t, S was 9 bits and the line read 9 250 1.
TEST(ClassScopeStructureTypedefSim,
     AMemberNamedByTheClassTypedefTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [7:0] nib_t;\n"
                       "class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

// The same with no typedef of the name outside the class, which left x sized
// by no typedef at all: one bit, S two, and the line 2 0 1.
TEST(ClassScopeStructureTypedefSim,
     AMemberNamedByTheClassTypedefAloneTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

// The class's nib_t reaches a member of a structure written inline within the
// typedef too, while a member written behind a package's name, p::nib_t, keeps
// the package's 6 bits (§26.3): S is 4 + 6 + 1 = 11 bits, and the parts of
// {4'd10, 6'd51, 1'b1} read back whole. With the inner member 8 bits wide,
// S was 15 bits and each part read a shifted slice.
TEST(ClassScopeStructureTypedefSim,
     AnInlineMemberTakesTheClassTypedefAndAPackageMemberItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [5:0] nib_t;\n"
                       "endpackage\n"
                       "typedef logic [7:0] nib_t;\n"
                       "class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed {\n"
                       "    struct packed { nib_t a; } inner;\n"
                       "    p::nib_t z;\n"
                       "    logic y;\n"
                       "  } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = {4'd10, 6'd51, 1'b1};\n"
                       "    $display(\"%0d %0d %0d %0d\", $bits(s), s.inner.a, "
                       "s.z, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "11 10 51 1\n");
}

// A typedef the class declares as the name of another typedef in its scope
// stands for that one: Box's pair_t is its own 4-bit nib_t, its three_t the
// 3-bit tri_t it inherits from Base (§8.13), and its pkg_t, written through
// package p (§26.3), p's 6-bit nib_t. Recorded as written, pair_t was sized
// by the compilation unit's 8-bit nib_t and three_t by no typedef at all.
TEST(ClassScopeTypedefNameSim, ATypedefNamedByAnotherTypedefInScopeTakesIt) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  typedef logic [5:0] nib_t;\n"
                 "endpackage\n"
                 "typedef logic [7:0] nib_t;\n"
                 "class Base;\n"
                 "  typedef logic [2:0] tri_t;\n"
                 "endclass\n"
                 "class Box extends Base;\n"
                 "  typedef logic [3:0] nib_t;\n"
                 "  typedef nib_t pair_t;\n"
                 "  typedef p::nib_t pkg_t;\n"
                 "  typedef tri_t three_t;\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial $display(\"%0d %0d %0d\", $bits(Box::pair_t), "
                 "$bits(Box::pkg_t), $bits(Box::three_t));\n"
                 "endmodule\n",
                 f),
      "4 6 3\n");
}

// The same with no typedef of the name outside the class, where pair_t
// reached no typedef at all.
TEST(ClassScopeTypedefNameSim, ATypedefNamedByAnotherClassTypedefAloneTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef nib_t pair_t;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", $bits(Box::pair_t));\n"
                       "endmodule\n",
                       f),
            "4\n");
}

// §23.9 has a package open a scope as a class does, so a structure typedef the
// package declares lays out a member written `nib_t` by the package's 4-bit
// nib_t, in a structure written inline within a member too: S and T are 5
// bits each, whatever the module reading them calls nib_t. Looked up bare,
// the member took a nib_t of the scope reading the type, or none. The
// package's forward typedef of its class C (§6.18) defines no type under p,
// and the class's full declaration still follows it.
TEST(PackageScopeStructureTypedefSim, AMemberNamedByThePackageTypedefTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef class C;\n"
                       "  class C; endclass\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  typedef struct packed {\n"
                       "    struct packed { nib_t a; } inner;\n"
                       "    logic y;\n"
                       "  } T;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  initial $display(\"%0d %0d\", $bits(p::S), "
                       "$bits(p::T));\n"
                       "endmodule\n",
                       f),
            "5 5\n");
}

// The same with no nib_t visible outside the package.
TEST(PackageScopeStructureTypedefSim,
     AMemberNamedByThePackageTypedefAloneTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", $bits(p::S));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

// §26.3 has an import make the package's S visible by its bare name, and the
// type it names is the one the package declared, its member x of p's 4-bit
// nib_t: s is 5 bits under the module's own 8-bit nib_t. Entered with the
// member's name bare, s took the module's nib_t and was 9 bits.
TEST(ImportedStructureTypedefSim, ANamedImportKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::S;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

// The same through a wildcard import, whose bare nib_t the module's own
// declaration below it hides.
TEST(ImportedStructureTypedefSim, AWildcardImportKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::*;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

// A named import with no nib_t visible in the module, where x took one bit
// and s two.
TEST(ImportedStructureTypedefSim, ANamedImportAloneKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::S;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

// §23.9 with §8.25: a parameterized class's structure typedef finds the
// class's own nib_t too, sized under the specialization's values: with W of
// 2, x is two 4-bit nib_t, S 9 bits, and 9'h1A5 keeps x at 210 and y at 1.
// Laid out by the design's table under the bare name, x reached no typedef
// and, its dimensions folding to nothing without W, took one bit.
TEST(ParameterizedClassStructureTypedefSim, AMemberTakesTheClassTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box #(int W = 2);\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1A5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "9 210 1\n");
}

// The same under a compilation-unit nib_t of 6 bits, which the bare lookup
// took instead, making S 13 bits. The class declares another typedef ahead of
// nib_t, which the search for nib_t passes over.
TEST(ParameterizedClassStructureTypedefSim,
     AMemberTakesTheClassTypedefOverTheUnits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [5:0] nib_t;\n"
                       "class Box #(int W = 2);\n"
                       "  typedef logic [7:0] byte_t;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1A5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "9 210 1\n");
}

// A class typedef that uses the class's parameter is sized by each
// specialization's own value (§8.25): w_t is 3 bits in Box #(3) and 5 in
// Box #(5), so S is 4 and 6 bits.
TEST(ParameterizedClassStructureTypedefSim,
     AMemberTakesTheClassTypedefUnderEachSpecialization) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box #(int W = 2);\n"
                       "  typedef logic [W-1:0] w_t;\n"
                       "  typedef struct packed { w_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #(3) a;\n"
                       "  Box #(5) b;\n"
                       "  initial begin\n"
                       "    a = new; b = new;\n"
                       "    $display(\"%0d %0d\", a.width(), b.width());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 6\n");
}

// A typedef the class inherits (§8.13) is found through its base, sized by
// the base's own values: Base's 4-bit nib_t makes Der's S 9 bits.
TEST(ParameterizedClassStructureTypedefSim, AMemberTakesAnInheritedTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Base;\n"
                       "  int k;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "endclass\n"
                       "class Der #(int W = 2) extends Base;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der #() d;\n"
                       "  initial begin d = new; $display(\"%0d\", d.width()); "
                       "end\n"
                       "endmodule\n",
                       f),
            "9\n");
}

// A member written through a package (§26.3) or by a typedef of the
// compilation unit the class does not redeclare keeps the type the design's
// table holds for it: 3 + 5 + 2 bits.
TEST(ParameterizedClassStructureTypedefSim,
     AMemberNamedOutsideTheClassKeepsItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [2:0] t3;\n"
                       "endpackage\n"
                       "typedef logic [4:0] t5;\n"
                       "class Box #(int W = 2);\n"
                       "  typedef struct packed { p::t3 a; t5 b; logic [W-1:0] "
                       "c; } S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; $display(\"%0d\", b.width()); "
                       "end\n"
                       "endmodule\n",
                       f),
            "10\n");
}

}  // namespace
