#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UserDefinedIndexAssocArraySimulation,
     StructureIndexIsKeyedByItsWholeValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { bit [15:0] hi; bit [63:0] lo; } k_t;\n"
      "  int m [k_t];\n"
      "  k_t a, b;\n"
      "  initial begin\n"
      "    a = '{hi: 1, lo: 0};\n"
      "    b = '{hi: 2, lo: 0};\n"
      "    m[a] = 1;\n"
      "    m[b] = 2;\n"
      "    $display(\"%0d %0d %0d\", m.num(), m[a], m[b]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1 2\n");
}

TEST(UserDefinedIndexAssocArraySimulation, ChandleIndexKeysAnEntry) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int m [chandle];\n"
      "  chandle h;\n"
      "  initial begin\n"
      "    m[h] = 7;\n"
      "    $display(\"%0d %0d %0d\", m.num(), m[h], m.exists(h));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 1\n");
}

TEST(UserDefinedIndexAssocArraySimulation, EventIndexKeysByTheObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int b [event];\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    b[e1] = 1;\n"
      "    b[e2] = 2;\n"
      "    b[null] = 3;\n"
      "    $display(\"%0d %0d %0d %0d\", b[e1], b[e2], b[null], b.num());\n"
      "    e2 = e1;\n"
      "    $display(\"%0d\", b[e2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 3\n1\n");
}

TEST(UserDefinedIndexAssocArraySimulation, UnknownBitInAnyElementIsInvalid) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {logic [3:0] a; int b;} s_t;\n"
      "  typedef struct {s_t n; logic [1:0] e [2];} o_t;\n"
      "  typedef logic [3:0] ld_t []; typedef logic [3:0] lq_t [$];\n"
      "  int m [s_t]; int n [s_t] = '{default: 7}; int o [o_t]; int d "
      "[ld_t];\n"
      "  s_t k, kz, kk; o_t ok; ld_t dk; lq_t qk; int qa [lq_t];\n"
      "  initial begin\n"
      "    k.a = 4'b10x1; k.b = 1; kz.a = 4'bz000; kz.b = 1;\n"
      "    kk.a = 4'b1011; kk.b = 1;\n"
      "    m[k] = 1; m[kz] = 2;\n"
      "    $display(\"%0d %0d %0d\", m.num(), m[k], n[k]);\n"
      "    ok.n = kk; ok.e[0] = 2'b1x; ok.e[1] = 0; o[ok] = 1;\n"
      "    ok.e[0] = 0; ok.n = k; o[ok] = 2;\n"
      "    dk = new[2]; dk[0] = 1; dk[1] = 4'bx; d[dk] = 1;\n"
      "    qk.push_back(1); qk.push_back(4'bx); qa[qk] = 1;\n"
      "    $display(\"%0d %0d %0d %0d\", o.num(), d.num(), qa.num(), "
      "m.exists(k));\n"
      "    m.delete(k); m[kk] = 5;\n"
      "    $display(\"%0d %0d\", m.num(), m[kk]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0 7\n0 0 0 0\n1 5\n");
  EXPECT_GE(f.diag.WarningCount(), 8u);
}

TEST(UserDefinedIndexAssocArraySimulation,
     EmptyAndNullMembersKeyTheirOwnEntries) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; endclass\n"
      "module t;\n"
      "  typedef struct {string s; int b;} ss_t;\n"
      "  typedef struct {C h; int b;} sc_t;\n"
      "  int m1 [ss_t]; int m2 [sc_t]; int m3 [chandle];\n"
      "  ss_t k1; sc_t k2; chandle ch;\n"
      "  initial begin\n"
      "    k1.s = \"\"; k1.b = 1; m1[k1] = 1; k1.s = \"x\"; m1[k1] = 2;\n"
      "    k1.s = \"\";\n"
      "    k2.h = null; k2.b = 1; m2[k2] = 1; k2.h = new; m2[k2] = 2;\n"
      "    k2.h = null;\n"
      "    ch = null; m3[ch] = 3;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", m1.num(), m2.num(), "
      "m3.num(), m1[k1], m2[k2], m3[ch]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 1 1 3\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UserDefinedIndexAssocArraySimulation,
     DISABLED_EmptyArrayIndexIsDistinctFromAOneElementArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef int id_t []; typedef int iq_t [$];\n"
      "  int m4 [id_t]; int m5 [iq_t]; id_t k4; iq_t k5;\n"
      "  initial begin\n"
      "    m4[k4] = 1; k4 = new[1]; m4[k4] = 2; k4 = {};\n"
      "    m5[k5] = 1; k5.push_back(0); m5[k5] = 2; k5 = {};\n"
      "    $display(\"%0d %0d %0d %0d\", m4.num(), m5.num(), m4[k4], "
      "m5[k5]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 1\n");
}

TEST(UserDefinedIndexAssocArraySimulation,
     DISABLED_StructureWithAnEmptyDynamicMemberKeysItsEntry) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int d []; int b;} sd_t;\n"
      "  int m6 [sd_t]; sd_t k6;\n"
      "  initial begin\n"
      "    k6.b = 1; m6[k6] = 1; k6.d = new[1]; m6[k6] = 2; k6.d = {};\n"
      "    $display(\"%0d %0d\", m6.num(), m6[k6]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UserDefinedIndexAssocArraySimulation,
     OrderWithoutARelationalOperatorIsStableWithinARun) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a; string s;} s_t;\n"
      "  typedef struct packed {bit [3:0] h; bit [3:0] l;} p_t;\n"
      "  int m [s_t]; int p [p_t]; s_t k; p_t pk; string o, r; int sum;\n"
      "  initial begin\n"
      "    k = '{5, \"e\"}; m[k] = 5; k = '{1, \"z\"}; m[k] = 1;\n"
      "    k = '{3, \"a\"}; m[k] = 3; k = '{2, \"q\"}; m[k] = 2;\n"
      "    foreach (m[i]) o = {o, $sformatf(\"%0d\", m[i])};\n"
      "    foreach (m[i]) r = {r, $sformatf(\"%0d\", m[i])};\n"
      "    $display(\"%0d %0d\", o == r, o.len());\n"
      "    r = \"\"; if (m.first(k)) do r = {r, $sformatf(\"%0d\", m[k])};\n"
      "      while (m.next(k));\n"
      "    $display(\"%0d\", o == r);\n"
      "    r = \"\"; if (m.last(k)) do r = {$sformatf(\"%0d\", m[k]), r};\n"
      "      while (m.prev(k));\n"
      "    $display(\"%0d\", o == r);\n"
      "    k = '{3, \"a\"}; m[k] = 3; void'(m.exists(k)); sum = m[k];\n"
      "    r = \"\"; foreach (m[i]) r = {r, $sformatf(\"%0d\", m[i])};\n"
      "    $display(\"%0d\", o == r);\n"
      "    k = '{7, \"b\"}; m[k] = 7; k = '{1, \"z\"}; m.delete(k);\n"
      "    r = \"\"; sum = 0;\n"
      "    foreach (m[i]) begin r = {r, $sformatf(\"%0d\", m[i])}; "
      "sum += m[i]; end\n"
      "    $display(\"%0d %0d %0d\", r.len(), m.num(), sum);\n"
      "    pk = 8'h31; p[pk] = 1; pk = 8'h05; p[pk] = 2; pk = 8'h20; "
      "p[pk] = 3;\n"
      "    r = \"\"; foreach (p[i]) r = {r, $sformatf(\"%0d\", p[i])};\n"
      "    $display(\"%s\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4\n1\n1\n1\n4 4 17\n231\n");
}

TEST(UserDefinedIndexAssocArraySimulation,
     UserDefaultReadAtAnUnknownIndexDoesNotWarn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {logic [3:0] a; int b;} s_t;\n"
      "  int n [s_t] = '{default: 7}; s_t k;\n"
      "  initial begin\n"
      "    k.a = 4'b10x1; k.b = 1;\n"
      "    $display(\"%0d %0d\", n[k], n.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 0\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
