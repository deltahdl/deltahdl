#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, FirstOnWildcardAssocArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[*];\n"
      "  int k;\n"
      "  initial k = aa.first(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "traversal method 'first' shall not be used on the "
                            "wildcard-indexed associative array 'aa'",
                            4, "7.9.4"));
}

TEST(BuiltinMethodElaboration, FirstOnIntKeyAssocArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.first(k);\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration,
     DISABLED_TraversalOnAWildcardArrayIsReportedInEveryPlace) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int w [*]; int x;\n"
      "  function void f(); void'(w.first(x)); endfunction\n"
      "endclass\n"
      "package p; int pw [*]; endpackage\n"
      "module t;\n"
      "  int w [*]; int x; K k;\n"
      "  function void g(); void'(w.last(x)); endfunction\n"
      "  initial begin\n"
      "    k = new; void'(k.w.next(x));\n"
      "    void'(p::pw.prev(x));\n"
      "  end\n"
      "  if (1) begin : gb\n"
      "    initial void'(w.first(x));\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "traversal method 'first' shall not be used",
                            3, "7.9.4"));
  EXPECT_TRUE(ReportedError(diags, "traversal method 'last' shall not be used",
                            8, "7.9.5"));
  EXPECT_TRUE(ReportedError(diags, "traversal method 'next' shall not be used",
                            10, "7.9.6"));
  EXPECT_TRUE(ReportedError(diags, "traversal method 'prev' shall not be used",
                            11, "7.9.7"));
  EXPECT_TRUE(ReportedError(diags, "traversal method 'first' shall not be used",
                            14, "7.9.4"));
}

}  // namespace
