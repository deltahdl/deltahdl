#include <gtest/gtest.h>

#include <string_view>
#include <utility>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

// §6.19.2's Table 6-10 (printed page 121) has a `name[N]` member generate the
// named constants name0 through nameN-1 and a `name[N:M]` member nameN through
// nameM, the written name naming no constant, and §26.6 (printed 815) makes an
// import of a declaration reached through an export an import of the original
// declaration. p2 hands on everything it imports from p1, so `p2::VAL2` and
// `p2::VAL1` name p1's constants. Before, PopulatePackageProvidedNames in
// src/elaborator/elaborator_scope_rules_names.cpp held the member under the
// written name VAL alone, and each read was reported as a name p2 neither
// declares nor exports; the "p1.VAL2" constant the registration records is
// keyed by the declaring package and answered for p1 only.
TEST(PackageImport, RangedEnumConstantsAreProvidedThroughAWildcardExport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int seen = VAL1 + VAL2;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p2::VAL2 + p2::VAL1;\n"
             "endmodule\n"));
}

// The written name of a ranged member declares nothing (printed 121), so
// §26.3's scope resolution operator (printed 808) finds no declaration of p1
// under it: `p1::VAL` is reported at its own line while `p1::VAL2`, one of
// the constants the member generates, is not. Before, the provided-name walk
// admitted VAL as a declaration of p1 and the read passed.
TEST(PackageScopeReference, WrittenNameOfARangedMemberIsNoDeclaration) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p1::VAL2;\n"
             "  initial r = p1::VAL;\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to 'p1::VAL2', which package 'p1' "
                             "neither declares nor exports",
                             6, "26.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p1::VAL', which package 'p1' "
                            "neither declares nor exports",
                            7, "26.3"));
}

// §26.3 (printed 810) makes every identifier a wildcard-imported package
// declares a candidate for a bare reference, and the constants a ranged
// member generates are such identifiers, for the `name[N]` form and the
// decrementing `name[N:M]` form alike (printed 121): VAL2 and W1 both resolve
// through the import, VAL2 the last of VAL0..VAL2 and W1 the last of W3..W1.
TEST(PackageImport, BareRangedEnumConstantResolvesThroughAWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3], W[3:1]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::*;\n"
             "  int r;\n"
             "  initial r = VAL2 + W1;\n"
             "endmodule\n"));
}

// §26.3 (printed 809-810) has an explicit import make the one identifier it
// names locally visible, and a generated constant is an identifier p1
// declares, so `import p1::VAL2;` brings VAL2 in for a bare read.
TEST(PackageImport, ExplicitImportOfARangedEnumConstantIsClean) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::VAL2;\n"
             "  int r;\n"
             "  initial r = VAL2;\n"
             "endmodule\n"));
}

// Counting the generated constants as the declaring package's admits nothing
// else and conflicts as §26.3 (printed 810) rules: p and q each generate VAL1
// from a ranged member of their own, so the bare read on line 11 matches an
// identifier the wildcard imports of two packages both define and is reported
// as ambiguous, as a plain member of each would be.
TEST(PackageImport, GeneratedEnumConstantsOfTwoImportsAreAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef enum {VAL[2]} t;\n"
             "endpackage\n"
             "package q;\n"
             "  typedef enum {VAL[2]} u;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  import q::*;\n"
             "  int r;\n"
             "  initial r = VAL1;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'VAL1' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            11, "26.3"));
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding it, and Syntax 6-5 makes the enum form
// a data_type, so p's `enum {X, Y} v;` declares X and Y in p as a typedef
// would; §26.3 (printed 810) then makes each a candidate the wildcard import
// brings in. The module elaborates clean, Y has the backing variable an
// imported literal is read through, and a local parameter reading Y folds to
// 1, the second member of a zero-based enumeration (printed 120). Before,
// EmitEnumLiteralsOfItems in src/elaborator/elaborator_typedef.cpp walked a
// package's typedefs alone, so Y had no backing variable in the module and
// the local parameter did not fold.
TEST(PackageImport, BareEnumDataDeclarationLiteralsComeThroughAWildcardImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  enum {X, Y} v;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int a = Y;\n"
      "  localparam int L = Y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindVar(design, "m", "Y"), nullptr);
  const auto* l = FindParam(design, "m", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_resolved);
  EXPECT_EQ(l->resolved_value, 1);
}

// A.2.1.3 gives one data declaration several declarators, and §6.19's own
// `enum {red, yellow, green} light1, light2;` declares its three constants
// once for the declaration rather than once per name, so the import brings Y
// in once: the module holds one backing variable for it.
TEST(PackageImport, ASharedEnumDeclarationImportsItsLiteralsOnce) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  enum {X, Y} v, w;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int a = Y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "Y"), 1u);
}

// §26.3 (printed 810) searches the locally visible identifiers, those the
// scope declared before the reference among them, ahead of the candidates a
// wildcard import supplies, so q's own VAL1, generated by its `VAL[2]`
// (Table 6-10, printed 121) and worth 1, is what q's local parameter reads,
// and not p's VAL1, worth 6 through `VAL[2] = 5`; a module reading `q::L`
// folds to 1 with no report. Before, NamesDeclaredBefore in
// src/elaborator/elaborator_enum_constants.cpp held the ranged member under
// its written name VAL alone, so BindPackageImportConstants took VAL1 for a
// name q had not declared and bound p's value over q's own, and L read 6.
TEST(PackageImport, OwnGeneratedEnumConstantShadowsAWildcardImportsInAPackage) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum {VAL[2] = 5} t;\n"
      "endpackage\n"
      "package q;\n"
      "  typedef enum {VAL[2]} u;\n"
      "  import p::*;\n"
      "  localparam int L = VAL1;\n"
      "endpackage\n"
      "module top;\n"
      "  localparam int M = q::L;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* m = FindParam(design, "top", "M");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_resolved);
  EXPECT_EQ(m->resolved_value, 1);
}

// §26.3 (printed page 808): the package scope resolution operator reaches a
// package's class without an import, so `p::C c;` in a module that imports
// nothing from p declares a handle of p's class, under the "p::C" key the
// simulator holds the class by. The elaborator marked a variable a handle only
// when the type's bare name was one the module's scope reached, which a class
// of a package the module does not import is not, so `c` was left a value of
// no class and its `new` constructed nothing.
TEST(PackageScopeReference, PackageQualifiedClassDeclaresAHandleWithoutImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  class C;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  p::C c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "p::C");
}

// §26.2 with §6.18: a package's typedef names a type as the package sees it,
// so B, declared `typedef C B;` in p, names p's C whatever a module importing
// p declares under the name C. Here the module's own C names p's B, and the
// elaborator, which looked B's type C up among the module's names, followed C
// to B and B back to C until the stack ran out (#5815); x is now p's C, four
// bits. A typedef of p already written behind a package's scope, q::T, keeps
// it, and names the module's nine-bit T no more than before.
TEST(PackageScopeReference, AnImportedTypedefNamesItsOwnPackagesTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q; typedef logic [1:0] T; endpackage\n"
      "package p;\n"
      "  typedef logic [3:0] C; typedef C B; typedef q::T S;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  typedef B C;\n"
      "  typedef logic [8:0] T;\n"
      "  C x; S y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 4u);
  const RtlirVariable* y = FindVar(design, "m", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 2u);
}

// §26.2 with §6.18: the same chain ending at a class of the package, whose
// handle the module's C declares, elaborates (#5815). The class's name K is
// no typedef of p, so B's C is p's typedef and C's K is left as written.
TEST(PackageScopeReference, AnImportedTypedefChainEndingAtAPackageClass) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package p; class K; virtual ifc vif; endclass typedef K C; "
      "typedef C B; endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef B C;\n"
      "  C x = new;\n"
      "  initial if (0) x.vif.t();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §26.3 (printed pages 809-810): a function body is a scope of its own, held
// to the import rules a module body is. Wildcard imports of two packages
// declaring c make a read of c ambiguous. Nothing in a body was checked.
TEST(PackageScopeReference, AmbiguousWildcardReadInAFunctionBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "package q; int c = 2; endpackage\n"
             "module m;\n"
             "  function int f();\n"
             "    import p::*;\n"
             "    import q::*;\n"
             "    return c;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'c' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            7, "26.3"));
}

// A declaration following a read the body's wildcard import resolved, here
// in the initializer of the declaration before it, is illegal in the body as
// in a module.
TEST(PackageScopeReference, DeclarationAfterAWildcardClaimInATaskBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  int r;\n"
             "  task t();\n"
             "    import p::*;\n"
             "    int a = c;\n"
             "    int c;\n"
             "    r = a;\n"
             "  endtask\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'c' follows a reference resolved "
                            "through a wildcard package import",
                            7, "26.3"));
}

// An explicit import of a name the body declares collides with it.
TEST(PackageScopeReference, ExplicitImportBesideALocalInAFunctionBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  function int f(int c);\n"
             "    import p::c;\n"
             "    return c;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p::c' collides with existing "
                            "declaration of 'c'",
                            4, "26.3"));
}

// A body whose import and declarations agree elaborates.
TEST(PackageScopeReference, FunctionBodyImportElaborates) {
  EXPECT_TRUE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  function automatic int f(int a);\n"
             "    import p::*;\n"
             "    int v = a;\n"
             "    return v + c;\n"
             "  endfunction\n"
             "endmodule\n"));
}

// §26.3 has an import make a package's declarations visible by their own
// names, a nettype among them, and §6.6.7 makes a declaration written with a
// nettype's name a net of that nettype. So n, under a wildcard import, and w,
// under an explicit one, are nets of P's nt resolving through P's pres. Under
// §6.22.6 n is of P's nt itself, so the pass switch joining it to a net of a
// nettype renaming P::nt joins nets of one nettype (#7599).
TEST(PackageImport, ImportedNettypeDeclaresANetOfThePackagesNettype) {
  ElabFixture f;
  auto* design = Elaborate(
      "package P;\n"
      "  function automatic logic pres(input logic d[]);\n"
      "    return d[0] & d[1];\n"
      "  endfunction\n"
      "  nettype logic nt with pres;\n"
      "endpackage\n"
      "module e;\n"
      "  import P::nt;\n"
      "  nt w;\n"
      "endmodule\n"
      "module m;\n"
      "  import P::*;\n"
      "  nettype P::nt pnt;\n"
      "  nt n;\n"
      "  pnt a;\n"
      "  tran sw(n, a);\n"
      "  e u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (const auto& [mod, name] :
       {std::pair<std::string_view, std::string_view>{"m", "n"}, {"e", "w"}}) {
    const RtlirNet* net = FindNet(design, mod, name);
    ASSERT_NE(net, nullptr) << name;
    EXPECT_TRUE(net->is_user_nettype) << name;
    EXPECT_EQ(net->resolve_func, "P::pres") << name;
  }
}

// §26.3 continues a search that fails in a scope into the next outer lexical
// scope, among the identifiers a wildcard import written there before the
// point of the reference offers, and §24.3 makes a program declared in a
// module a scope nested in it. So the program's call of set_v finds the task
// the module imports from pkg above the program. Its own items holding no
// import, it was reported as an undeclared identifier.
TEST(PackageImport, ANestedProgramCallsATaskItsModuleWildcardImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial set_v(v);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The same through an explicit import of the task.
TEST(PackageImport, ANestedProgramCallsATaskItsModuleExplicitlyImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::set_v;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial set_v(v);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The search goes on through each outer lexical scope in turn (§26.3): a
// program in a module nested in top reaches the import top writes above the
// nested module.
TEST(PackageImport, ANestedProgramCallsATaskAnOuterModuleImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  module mid;\n"
      "    logic [7:0] v;\n"
      "    program p;\n"
      "      initial set_v(v);\n"
      "    endprogram\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
