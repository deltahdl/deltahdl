#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocArrayDeleteElaboration,
     DISABLED_IndexArgumentOfARefusedTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class U; endclass\n"
      "module t;\n"
      "  int ms [string]; int mc [C]; int mi [int]; int mw [*];\n"
      "  int i; U u; real r; shortreal sr; string s;\n"
      "  initial begin\n"
      "    ms.delete(5);\n"
      "    ms.delete(i);\n"
      "    mc.delete(i);\n"
      "    mc.delete(s);\n"
      "    mc.delete(u);\n"
      "    mi.delete(2.5);\n"
      "    mi.delete(sr);\n"
      "    mw.delete(r);\n"
      "    mw.delete(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 7; line <= 15; ++line) {
    EXPECT_TRUE(
        ReportedError(diags, "index argument of 'delete'", line, "7.9.2"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 9u);
}

TEST(AssocArrayDeleteElaboration,
     DISABLED_IndexArgumentOfARefusedTypeIsReportedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "class K;\n"
      "  int ms [string];\n"
      "  function void f(); ms.delete(5); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ms [string]; K k;\n"
      "  task tk; ms.delete(5); endtask\n"
      "  initial begin k = new; k.ms.delete(5); end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : {3u, 7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(diags, "index argument of 'delete'", line, "7.9.2"))
        << line;
  }
}

TEST(AssocArrayDeleteElaboration, IndexArgumentOfAnAcceptedTypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module t;\n"
      "  int ms [string]; int mc [C]; int mi [int]; int mw [*];\n"
      "  string s; C c; D d; byte b; longint l;\n"
      "  initial begin\n"
      "    ms.delete(\"x\"); ms.delete(\"\"); ms.delete(s);\n"
      "    mc.delete(c); mc.delete(d); mc.delete(null);\n"
      "    mi.delete(b); mi.delete(l); mi.delete(int'(2.5));\n"
      "    mw.delete(b); mw.delete(l); mw.delete(40'h1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
