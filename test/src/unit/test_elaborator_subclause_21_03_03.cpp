#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringFormatTaskElaboration, SwriteStringOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial $swrite(s, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteIntegralOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] v;\n"
      "  initial $swrite(v, \"%h\", 8'hab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteUnpackedByteArrayOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b [0:3];\n"
      "  initial $swrite(b, \"ABCD\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $swrite(r, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$swrite/$sformat cannot write its text into a real "
                    "variable; give it an integral, string or "
                    "unpacked byte array target",
                    3, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SformatRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $sformat(r, \"v=%0d\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$swrite/$sformat cannot write its text into a real "
                    "variable; give it an integral, string or "
                    "unpacked byte array target",
                    3, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SformatfHasNoOutputVarCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"val=%0d\", 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration,
     SwriteRealOutputVarInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real acc;\n"
      "  logic ready;\n"
      "  initial assert (ready) $swrite(acc, \"n=%0d\", 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 4, "21.3.3"));
}

TEST(StringFormatTaskElaboration,
     SformatRealOutputVarInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real tally;\n"
      "  logic done;\n"
      "  initial assert (done) else $sformat(tally, \"t=%0d\", 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 4, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SwritebRealOutputVarInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real gauge;\n"
      "  initial randcase 3: $swriteb(gauge, \"%b\", 4'b1010); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 3, "21.3.3"));
}

TEST(StringFormatTaskElaboration,
     SwritehRealOutputVarInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real level;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $swriteh(level, \"%h\", 8'hab); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 5, "21.3.3"));
}

constexpr const char* kTargetKinds =
    "give it an integral, string or unpacked byte array target";

void ExpectTargetRejected(const std::string& src, uint32_t line) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTargetKinds, line, "21.3.3"))
      << src;
}

void ExpectReportedWith(const std::string& src, const std::string& message,
                        uint32_t line) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "21.3.3"))
      << src;
}

void ExpectElaboratesCleanly(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_FALSE(f.has_errors) << src;
}

TEST(StringFormatTaskElaboration, SwriteoRealOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  real r;\n"
      "  initial $swriteo(r, 8'o17);\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_RealOutputVarInAFunctionRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  function void put(); real r; $swrite(r, 1); endfunction\n"
      "endmodule\n",
      2);
}

TEST(StringFormatTaskElaboration, RealOutputVarInATaskRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  real r;\n"
      "  task put(); $sformat(r, \"%0d\", 1); endtask\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration,
     DISABLED_RealPropertyOutputVarInAClassMethodRejected) {
  ExpectTargetRejected(
      "class C;\n"
      "  real r;\n"
      "  function void put(); $swriteh(r, 4'hc); endfunction\n"
      "endclass\n",
      3);
}

TEST(StringFormatTaskElaboration,
     DISABLED_RealOutputVarInAPackageFunctionRejected) {
  ExpectTargetRejected(
      "package k;\n"
      "  real r;\n"
      "  function void put(); $swriteb(r, 2'b10); endfunction\n"
      "endpackage\n",
      3);
}

TEST(StringFormatTaskElaboration, ShortrealOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  shortreal r;\n"
      "  initial $swrite(r, 1);\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, RealtimeOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  realtime r;\n"
      "  initial $sformat(r, \"%0d\", 1);\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_UnpackedIntArrayOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  int a[4];\n"
      "  initial $swrite(a, \"ABCD\");\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_UnpackedStructOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  struct { byte a; byte b; } u;\n"
      "  initial $sformat(u, \"AB\");\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_ClassHandleOutputVarRejected) {
  ExpectTargetRejected(
      "class C; endclass\n"
      "module m;\n"
      "  C h;\n"
      "  initial $swrite(h, \"x\");\n"
      "endmodule\n",
      4);
}

TEST(StringFormatTaskElaboration, DISABLED_EventOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  event e;\n"
      "  initial $swrite(e, \"x\");\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_ChandleOutputVarRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  chandle c;\n"
      "  initial $sformat(c, \"x\");\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, DISABLED_LiteralFirstArgumentRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  initial $swrite(5, \"x\");\n"
      "endmodule\n",
      2);
}

TEST(StringFormatTaskElaboration,
     DISABLED_OperatorExpressionFirstArgumentRejected) {
  ExpectTargetRejected(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial $sformat(a | b, \"x\");\n"
      "endmodule\n",
      3);
}

TEST(StringFormatTaskElaboration, EveryAllowedKindOfOutputVarIsAccepted) {
  ExpectElaboratesCleanly(
      "typedef struct packed { byte a; byte b; } ps_t;\n"
      "module m;\n"
      "  byte q[$];\n"
      "  byte d[];\n"
      "  byte u[0:1];\n"
      "  ps_t p;\n"
      "  int i;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(q, \"AB\");\n"
      "    $sformat(d, \"AB\");\n"
      "    $swriteo(u, \"AB\");\n"
      "    $swriteh(p, \"AB\");\n"
      "    $swriteb(i, \"AB\");\n"
      "    $sformat(s, \"AB\");\n"
      "  end\n"
      "endmodule\n");
}

TEST(StringFormatTaskElaboration, AnAllowedOutputVarIsAcceptedInEveryPlace) {
  ExpectElaboratesCleanly(
      "package k;\n"
      "  string s;\n"
      "  function void put(); $swrite(s, 1); endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  int i;\n"
      "  function void put(); $sformat(i, \"%0d\", 1); endfunction\n"
      "endclass\n"
      "interface ifc;\n"
      "  string s;\n"
      "  initial $swriteh(s, 1);\n"
      "endinterface\n"
      "program p;\n"
      "  string s;\n"
      "  initial $swriteo(s, 1);\n"
      "endprogram\n"
      "module m;\n"
      "  logic [15:0] v;\n"
      "  task put(); $swriteb(v, 1); endtask\n"
      "  for (genvar g = 0; g < 2; g++) begin : gen\n"
      "    string t;\n"
      "    initial $sformat(t, \"%0d\", g);\n"
      "  end\n"
      "endmodule\n");
}

TEST(StringFormatTaskElaboration, DISABLED_SwriteWithNoArgumentIsReported) {
  for (const char* name : {"$swrite", "$swriteb", "$swriteh", "$swriteo"}) {
    ExpectReportedWith(
        "module m;\n  initial " + std::string(name) + "();\nendmodule\n",
        std::string(name) + " takes an output variable", 2);
  }
}

TEST(StringFormatTaskElaboration, DISABLED_SwriteWithNoParenthesesIsReported) {
  for (const char* name : {"$swrite", "$swriteb", "$swriteh", "$swriteo"}) {
    ExpectReportedWith(
        "module m;\n  initial " + std::string(name) + ";\nendmodule\n",
        std::string(name) + " takes an output variable", 2);
  }
}

TEST(StringFormatTaskElaboration, DISABLED_SformatWithNoArgumentIsReported) {
  ExpectReportedWith(
      "module m;\n"
      "  initial $sformat();\n"
      "endmodule\n",
      "$sformat takes an output variable and a format string", 2);
}

TEST(StringFormatTaskElaboration, DISABLED_SformatWithNoFormatIsReported) {
  ExpectReportedWith(
      "module m;\n"
      "  string s;\n"
      "  initial $sformat(s);\n"
      "endmodule\n",
      "$sformat takes an output variable and a format string", 3);
}

TEST(StringFormatTaskElaboration, DISABLED_SformatfWithNoFormatIsReported) {
  ExpectReportedWith(
      "module m;\n"
      "  string s;\n"
      "  initial s = $sformatf();\n"
      "endmodule\n",
      "$sformatf takes a format string", 3);
}

TEST(StringFormatTaskElaboration, TheShortestAllowedCallsAreAccepted) {
  ExpectElaboratesCleanly(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s);\n"
      "    $swriteb(s);\n"
      "    $swriteh(s);\n"
      "    $swriteo(s);\n"
      "    $sformat(s, \"x\");\n"
      "    s = $sformatf(\"x\");\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
