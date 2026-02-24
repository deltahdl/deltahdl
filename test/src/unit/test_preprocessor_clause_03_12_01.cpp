// §3.12.1: Compilation units

#include <gtest/gtest.h>
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string &src, PreprocFixture &f,
                              PreprocConfig config = {}) {

  auto fid = f.mgr.AddFile("<test>", src);

  Preprocessor pp(f.mgr, f.diag, std::move(config));

  return pp.Preprocess(fid);

namespace {

// 7. Compiler directives apply within a CU only.
// A `define in one parse (CU) does not leak into a separate parse (CU).
TEST(ParserClause03, Cl3_12_1_DirectivesLocalToCU) {
  // First CU: define a macro and use it.
  auto r1 = Parse(
      "`define FOO 1\n"
      "module m1;\n"
      "  localparam X = `FOO;\n"
      "endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  // Second CU (separate Parse call): macro should NOT be defined.
  // Using `FOO without defining it should produce a preprocessor error.
  auto r2 = Parse(
      "module m2;\n"
      "  localparam Y = `FOO;\n"
      "endmodule\n");
  // The undefined macro should cause an error in the second CU.
  EXPECT_TRUE(r2.has_errors);
}

}  // namespace
