#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5 creates bins automatically for a coverpoint of an integral expression
// only, so a coverpoint of a real expression is left without bins unless it
// declares an explicit `bins` of its own. The expression is real when it names
// a real variable or a real covergroup formal, or when an operand of its
// arithmetic is real; an explicit data type before the label decides the
// coverpoint's type in place of the expression's. An ignore_bins item is not a
// `bins` construct, and a comparison of real operands is integral.
TEST(RealCoverpointBins, RealCoverpointWithoutBinsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg (real fr);\n"
      "    coverpoint r;\n"
      "    scaled: coverpoint i * 0.5;\n"
      "    sum: coverpoint i + r;\n"
      "    formal: coverpoint fr;\n"
      "    real typed: coverpoint i;\n"
      "    ignored: coverpoint r { ignore_bins z = {0.0}; }\n"
      "    coverpoint i;\n"
      "    int narrowed: coverpoint r;\n"
      "    binned: coverpoint r { option.weight = 2; bins a = {[0.0:1.0]}; }\n"
      "    cmp: coverpoint r > 1.0;\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u, 8u, 9u, 10u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "nothing creates bins for a coverpoint of a real "
                      "expression, so declare at least one 'bins' for it",
                      line, "19.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

// §19.5 and §19.6 hold of a covergroup embedded in a class (§19.4) as of one a
// module declares. Its names are the class's properties and then the
// declarations of the scope that declares the class: a real property, a real
// variable of the enclosing module, and a name neither declares, wherever the
// class stands -- at compilation-unit scope, in a package or in a module.
TEST(RealCoverpointBins, EmbeddedCovergroupsAreCheckedLikeModuleOnes) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class D;\n"
      "    bit w;\n"
      "    covergroup dg;\n"
      "      cw: coverpoint w;\n"
      "      x: cross cw, nope;\n"
      "    endgroup\n"
      "    function new(); dg = new; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "class C;\n"
      "  real r;\n"
      "  covergroup cg;\n"
      "    coverpoint r;\n"
      "  endgroup\n"
      "  function new(); cg = new; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  real mr;\n"
      "  bit b;\n"
      "  class E;\n"
      "    covergroup eg;\n"
      "      coverpoint b;\n"
      "      y: cross mr, b;\n"
      "    endgroup\n"
      "    function new(); eg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'nope' is neither a coverpoint of "
                            "covergroup 'dg' nor a variable",
                            6, "19.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nothing creates bins for a coverpoint of a real "
                            "expression, so declare at least one 'bins' for it",
                            14, "19.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross item 'mr' is a real variable, which a cross "
                            "can reach only through a coverpoint",
                            24, "19.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
