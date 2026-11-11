#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocArrayExistsElaboration,
     DISABLED_IndexArgumentOfARefusedTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class U; endclass\n"
      "module t;\n"
      "  int ms [string]; int mc [C]; int mi [int]; int mw [*];\n"
      "  int i; U u; real r; shortreal sr; string s; int e;\n"
      "  initial begin\n"
      "    e = ms.exists(5);\n"
      "    e = ms.exists(i);\n"
      "    e = mc.exists(i);\n"
      "    e = mc.exists(s);\n"
      "    e = mc.exists(u);\n"
      "    e = mi.exists(2.5);\n"
      "    e = mi.exists(sr);\n"
      "    e = mw.exists(r);\n"
      "    e = mw.exists(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 7; line <= 15; ++line) {
    EXPECT_TRUE(
        ReportedError(diags, "index argument of 'exists'", line, "7.9.3"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 9u);
}

TEST(AssocArrayExistsElaboration,
     DISABLED_IndexArgumentOfARefusedTypeIsReportedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int ms [string];\n"
      "  function int f(); return ms.exists(5); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ms [string]; K k; int e;\n"
      "  task tk; e = ms.exists(5); endtask\n"
      "  initial begin k = new; e = k.ms.exists(5); end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {3u, 7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(diags, "index argument of 'exists'", line, "7.9.3"))
        << line;
  }
}

TEST(AssocArrayExistsElaboration, IndexArgumentOfAnAcceptedTypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module t;\n"
      "  int ms [string]; int mc [C]; int mi [int]; int mw [*];\n"
      "  string s; C c; D d; byte b; longint l; int e;\n"
      "  initial begin\n"
      "    e = ms.exists(\"x\") + ms.exists(\"\") + ms.exists(s);\n"
      "    e = mc.exists(c) + mc.exists(d) + mc.exists(null);\n"
      "    e = mi.exists(b) + mi.exists(l) + mi.exists(int'(2.5));\n"
      "    e = mw.exists(b) + mw.exists(l) + mw.exists(40'h1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
