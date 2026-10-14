#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.3 (footnote 29): the extends specification of a covergroup is allowed
// only within a class. The Annex A grammar accepts `covergroup extends base ;`
// in any scope, so the restriction is applied at elaboration. A derived
// covergroup declared at module scope has no enclosing class and is illegal.
TEST(CovergroupExtendsScope, ExtendsInModuleError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  covergroup extends base_cg;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a covergroup may only use 'extends' inside a class", 2, "19.3"));
}

// §19.3 (footnote 29): a covergroup that does NOT use extends is legal at
// module scope, so the check must not reject an ordinary covergroup.
TEST(CovergroupExtendsScope, NonExtendsCovergroupInModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [2:0] addr;\n"
             "  covergroup cg @(addr);\n"
             "    coverpoint addr;\n"
             "  endgroup\n"
             "endmodule\n"));
}

// §19.3 (footnote 29): the extends form is permitted within a class. The base
// covergroup is defined in a superclass, so the derived embedded covergroup
// elaborates without the "outside class" error.
TEST(CovergroupExtendsScope, ExtendsInsideClassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  covergroup extends cg;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §19.3: an instance of a covergroup is given by `new` an actual for each
// formal that has no default, in a declaration, a procedural assignment and an
// automatic variable's initializer alike.
TEST(CovergroupNewActuals, FormalWithoutDefaultLeftWithoutActualIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v;\n"
      "  covergroup cg (int lo);\n"
      "    coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  cg d = new(3);\n"
      "  initial begin\n"
      "    automatic cg e = new();\n"
      "    c = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "new of covergroup 'cg' gives no actual to "
                              "formal 'lo', which has no default",
                              line, "19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §19.3 with §13.5: each actual of a covergroup's `new` binds a formal, so a
// positional actual past the last formal and a named one naming no formal are
// errors; the named one leaves `lo` without an actual besides.
TEST(CovergroupNewActuals, ActualBindingNoFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v;\n"
      "  covergroup cg (int lo);\n"
      "    coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3, 4);\n"
      "  cg d = new(.hi(3));\n"
      "  cg e = new(.lo(3));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "new of covergroup 'cg' is given 2 actuals for its "
                            "1 formals",
                            6, "19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'cg' has no formal 'hi'", 7, "19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "new of covergroup 'cg' gives no actual to formal "
                            "'lo', which has no default",
                            7, "19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §19.3 with §13.5.2: a covergroup's ref formal is passed a variable, so an
// expression, a literal and a net are errors as its actual.
TEST(CovergroupNewActuals, RefFormalGivenNoVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  int v;\n"
      "  covergroup cg (ref int x);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  cg a = new(v + 1);\n"
      "  cg b = new(5);\n"
      "  cg c = new(w);\n"
      "  cg d = new(v);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the actual of ref formal 'x' of covergroup 'cg' "
                              "is no variable",
                              line, "19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §19.3: the formals of a covergroup are visible within its declaration
// alone, so reading one through an instance is an error.
TEST(CovergroupFormals, FormalReadThroughAnInstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v, w;\n"
      "  covergroup cg (int lo);\n"
      "    cp: coverpoint v { bins b = {[lo:9]}; }\n"
      "  endgroup\n"
      "  cg c = new(3);\n"
      "  initial begin\n"
      "    w = c.lo;\n"
      "    c.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'lo' is a formal of covergroup 'cg', which is not "
                            "visible through instance 'c'",
                            8, "19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
