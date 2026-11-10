#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(Elaboration, StringVarIsString) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "s") {
      found = true;
      EXPECT_TRUE(v.is_string);
    }
  }
  EXPECT_TRUE(found) << "string variable 's' not found";
}

TEST(Elaboration, StringDefaultEmptyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, StringWithLiteralInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s = \"test\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, StringReplicationXZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = {1'bx{\"ab\"}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(Elaboration, StringVarMayBeIndexedForReadingAndWriting) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"world\";\n"
             "  byte c;\n"
             "  initial begin\n"
             "    c = s[2];\n"
             "    s[1] = \"a\";\n"
             "  end\n"
             "endmodule\n"));
}

TEST(Elaboration, IndexingAVarOfTypedefedStringType) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef string str_t;\n"
             "  str_t s = \"world\";\n"
             "  byte c;\n"
             "  initial c = s[2];\n"
             "endmodule\n"));
}

TEST(Elaboration, IndexingAScalarLogicVarIsStillRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s;\n"
      "  logic c;\n"
      "  initial c = s[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

TEST(Elaboration, StringParameterConcatenationFoldsToTheJoinedCharacters) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam string P = \"ab\";\n"
      "  localparam string Q = {P, \"c\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

TEST(Elaboration, StringParameterConcatenationFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"ab\";\n"
      "      localparam string Q = {P, \"c\"};\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

void ExpectStringNumericAssignIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  string s;\n  int n;\n  logic ok;\n"
      "  initial\n    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type-incompatible assignment between string and numeric type",
      LineHolding(src, "s = n;"), "6.16"));
}

TEST(Elaboration, StringNumericAssignInAnAssertionPassStmt) {
  ExpectStringNumericAssignIn("assert (ok) s = n;");
}

TEST(Elaboration, StringNumericAssignInAnAssertionFailStmt) {
  ExpectStringNumericAssignIn("assert (ok) else s = n;");
}

TEST(Elaboration, StringNumericAssignInARandcaseItem) {
  ExpectStringNumericAssignIn("randcase 1: s = n; endcase");
}

TEST(Elaboration, StringNumericAssignInARandsequenceCodeBlock) {
  ExpectStringNumericAssignIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { s = n; };\n"
      "      endsequence\n"
      "    end");
}

TEST(Elaboration, StringNumericAssignInARandsequenceWeightCodeBlock) {
  ExpectStringNumericAssignIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { s = n; };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(Elaboration, UncastStringIntegralAssignmentOfAnyShapeReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {string a;} T;\n"
      "  int n = 1;\n"
      "  real r;\n"
      "  string s = \"ab\";\n"
      "  string t = n;\n"
      "  string sa[2];\n"
      "  int arr[];\n"
      "  T st;\n"
      "  chandle ch;\n"
      "  function automatic void f();\n"
      "    s = 8'h41;\n"
      "  endfunction\n"
      "  function automatic int g();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    string u;\n"
      "    string w = n;\n"
      "    s = n + 1;\n"
      "    s <= 1.5;\n"
      "    s[0] = t;\n"
      "    n = t.substr(0, 1);\n"
      "    sa[0] = t;\n"
      "    n = t.len();\n"
      "    arr = new[2];\n"
      "    n = arr.size();\n"
      "    n = g();\n"
      "    n = st.a[0];\n"
      "    n = (s == t);\n"
      "    s = \"x\";\n"
      "    ch = null;\n"
      "    n = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "type-incompatible assignment between string and numeric type";
  for (uint32_t line : {6U, 12U, 19U, 20U, 21U, 22U, 23U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.16"));
  }
  for (uint32_t line : {24U, 25U, 26U, 27U, 28U, 29U, 30U, 31U, 32U, 33U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.16"));
  }
}

TEST(StringMethodElaboration, NameNoStringMethodIsReported) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  string s;\n"
      "  string sa [2];\n"
      "  initial begin\n"
      "    s.foo();\n"
      "    s.h.run();\n"
      "    sa[1].bar();\n"
      "    s.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 's'", 5, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the string 's'", 6, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the string 'sa'", 7, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'rand_mode' is not a built-in method of the string 's'", 8,
      "6.16"));
}

TEST(StringMethodElaboration, EveryStringMethodIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  string sa [2];\n"
             "  integer i;\n"
             "  real r;\n"
             "  byte b;\n"
             "  initial begin\n"
             "    i = s.len();\n"
             "    s.putc(0, b);\n"
             "    b = s.getc(0);\n"
             "    s = s.toupper();\n"
             "    s = s.tolower();\n"
             "    i = s.compare(\"a\");\n"
             "    i = s.icompare(\"a\");\n"
             "    s = s.substr(0, 1);\n"
             "    i = s.atoi();\n"
             "    i = s.atohex();\n"
             "    i = s.atooct();\n"
             "    i = s.atobin();\n"
             "    r = s.atoreal();\n"
             "    s.itoa(1);\n"
             "    s.hextoa(1);\n"
             "    s.octtoa(1);\n"
             "    s.bintoa(1);\n"
             "    s.realtoa(1.0);\n"
             "    i = sa[0].len();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StringMethodElaboration, FormalsAndBlockVariablesAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function void g(string a);\n"
      "    a.foo();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    string b;\n"
      "    b.bar();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 'a'", 3, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the string 'b'", 7, "6.16"));
}

TEST(StringMethodElaboration, AnsiPortsAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m(input string s, input string q [2]);\n"
      "  initial begin\n"
      "    s.foo();\n"
      "    q[0].baz();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 's'", 3, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'baz' is not a built-in method of the string 'q'", 4, "6.16"));
}

TEST(StringMethodElaboration, MethodOfAStringACallReturnsIsReported) {
  ElabFixture f;
  ElabOk(
      "package q;\n"
      "  function string pf(); return \"q\"; endfunction\n"
      "endpackage\n"
      "function string uf(); return \"u\"; endfunction\n"
      "class K;\n"
      "  function K me(); return this; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  typedef string sa_t [2];\n"
      "  function string g(); return \"g\"; endfunction\n"
      "  function sa_t ga(); sa_t v; return v; endfunction\n"
      "  process p;\n"
      "  K k = new;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    g().foo();\n"
      "    p.get_randstate().bar();\n"
      "    n = g().len() + ga().unique().size() + ga()[0].len();\n"
      "    n = q::pf().len() + uf().len() + s.substr(0, 1).len();\n"
      "    n = k.get_randstate().len();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string that 'g()' returns",
      18, "6.16"));
  EXPECT_TRUE(ReportedError(diags,
                            "'bar' is not a built-in method of the string that "
                            "'get_randstate()' returns",
                            19, "6.16"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(StringMethodElaboration, NonAnsiPortsAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m(s, .a(t));\n"
      "  input string s;\n"
      "  input string t;\n"
      "  initial begin\n"
      "    s.foo();\n"
      "    t.bar();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 's'", 5, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the string 't'", 6, "6.16"));
}

TEST(StringMethodElaboration, PackageScopeIsNoSelectFromAString) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  string p;\n"
             "  int y;\n"
             "  initial y = p::x;\n"
             "endmodule\n"));
}

constexpr std::string_view kStringToNumeric =
    "type-incompatible assignment between string and numeric type";

::testing::AssertionResult StringRuleReportedOn(const std::string& src,
                                                std::string_view marker) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), kStringToNumeric,
                       LineHolding(src, marker), "6.16");
}

TEST(Elaboration,
     AStringWrittenToACharacterInAnInterfaceProgramOrModuleIsReported) {
  EXPECT_TRUE(StringRuleReportedOn(
      "interface ifc;\n  string a, b;\n  initial a[0] = b;\nendinterface\n"
      "module t;\n  ifc i();\nendmodule\n",
      "a[0] = b"));
  EXPECT_TRUE(StringRuleReportedOn(
      "program pg;\n  string a, b;\n  initial a[0] = b;\nendprogram\n"
      "module t;\n  pg u();\nendmodule\n",
      "a[0] = b"));
  EXPECT_TRUE(StringRuleReportedOn(
      "module t;\n  string a, b;\n  initial a[0] = b;\nendmodule\n",
      "a[0] = b"));
}

TEST(
    Elaboration,
    DISABLED_AStringWrittenToACharacterInAClassPackageUnitOrGenerateBlockIsReported) {
  EXPECT_TRUE(StringRuleReportedOn(
      "class C;\n  string a, b;\n  function void f();\n    a[0] = b;\n"
      "  endfunction\nendclass\nmodule t;\nendmodule\n",
      "a[0] = b"));
  EXPECT_TRUE(StringRuleReportedOn(
      "package k;\n  string a, b;\n  function void f();\n    a[0] = b;\n"
      "  endfunction\nendpackage\nmodule t;\nendmodule\n",
      "a[0] = b"));
  EXPECT_TRUE(StringRuleReportedOn(
      "string a, b;\nfunction void f();\n  a[0] = b;\nendfunction\n"
      "module t;\nendmodule\n",
      "a[0] = b"));
  EXPECT_TRUE(
      StringRuleReportedOn("module t;\n  if (1) begin : g\n    string a, b;\n"
                           "    initial a[0] = b;\n  end\nendmodule\n",
                           "a[0] = b"));
}

TEST(Elaboration,
     ACharacterOrALiteralWrittenToACharacterIsAcceptedInEveryPlace) {
  EXPECT_TRUE(ElabOk(
      "class C;\n  string a, b;\n  function void f();\n    a[0] = b[0];\n"
      "  endfunction\nendclass\npackage k;\n  string a;\n"
      "  function void f();\n    a[0] = \"h\";\n  endfunction\nendpackage\n"
      "string ua;\nbyte ub;\nfunction void f();\n  ua[0] = ub;\nendfunction\n"
      "interface ifc;\n  string a;\n  initial a[1] = 8'h41;\nendinterface\n"
      "module t;\n  ifc i();\n  if (1) begin : g\n    string a;\n"
      "    initial a[0] = 66;\n  end\nendmodule\n"));
}

TEST(Elaboration,
     DISABLED_ANonConstantReplicationOfLiteralsIntoAnIntegralIsReported) {
  EXPECT_TRUE(
      StringRuleReportedOn("module t;\n  logic [15:0] r;\n  integer i = 2;\n"
                           "  initial r = {i{\"Hi\"}};\nendmodule\n",
                           "r = {i"));
  EXPECT_TRUE(StringRuleReportedOn(
      "class C;\n  logic [15:0] r;\n  int i = 2;\n  function void f();\n"
      "    r = {i{\"Hi\"}};\n  endfunction\nendclass\nmodule t;\nendmodule\n",
      "r = {i"));
  EXPECT_TRUE(StringRuleReportedOn(
      "package k;\n  logic [15:0] r;\n  int i = 2;\n  function void f();\n"
      "    r = {i{\"Hi\"}};\n  endfunction\nendpackage\nmodule t;\nendmodule\n",
      "r = {i"));
}

TEST(Elaboration,
     ReplicationsOfStringsIntoStringsOrConstantLiteralsAreAccepted) {
  EXPECT_TRUE(ElabOk(
      "module t;\n  logic [31:0] r;\n  integer i = 2;\n  string a, b = \"x\";\n"
      "  initial begin\n    a = {i{\"Hi\"}};\n    a = {i{b}};\n"
      "    r = {2{\"Hi\"}};\n    a = {5{\"Hi\"}};\n    a = {a, b};\n"
      "    a = {\"Hi\", b};\n  end\nendmodule\n"));
}

TEST(Elaboration,
     DISABLED_AZeroReplicationOfStringsStandsAloneAsTheEmptyString) {
  EXPECT_TRUE(ElabOk(
      "module t;\n  parameter string P = {0{\"ab\"}};\n  string s, b = \"x\";\n"
      "  int n;\n  initial begin\n    s = {0{\"ab\"}};\n    s = {0{b}};\n"
      "    s = {0{\"ab\", \"c\"}};\n    n = {0{\"ab\"}} == \"\";\n  end\n"
      "endmodule\n"));
}

}  // namespace
