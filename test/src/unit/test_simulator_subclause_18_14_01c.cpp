#include <gtest/gtest.h>

#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::vector<std::string> Lines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  return lines;
}

const char* const kItem =
    "class Item;\n"
    "  rand bit [31:0] v;\n"
    "endclass\n";

TEST(RandomStabilityPropertiesCases,
     InterfaceStaticInitializerObjectsMatchAcrossInstances) {
  EXPECT_EQ(
      RunSrc(std::string(kItem) + "interface ifc;\n"
                                  "  Item o = new;\n"
                                  "endinterface\n"
                                  "module t;\n"
                                  "  ifc a();\n"
                                  "  ifc b();\n"
                                  "  initial begin\n"
                                  "    void'(a.o.randomize());\n"
                                  "    void'(b.o.randomize());\n"
                                  "    $display(\"%0d\", a.o.v == b.o.v);\n"
                                  "  end\n"
                                  "endmodule\n"),
      "1\n");
}

TEST(RandomStabilityPropertiesCases,
     ProgramStaticInitializerObjectsMatchAcrossInstances) {
  const std::vector<std::string> kLines =
      Lines(RunSrc(std::string(kItem) + "program pg;\n"
                                        "  Item o = new;\n"
                                        "  initial begin\n"
                                        "    void'(o.randomize());\n"
                                        "    $display(\"%h\", o.v);\n"
                                        "  end\n"
                                        "endprogram\n"
                                        "module t;\n"
                                        "  pg a();\n"
                                        "  pg b();\n"
                                        "endmodule\n"));
  ASSERT_EQ(kLines.size(), 2u);
  EXPECT_EQ(kLines[0], kLines[1]);
}

const char* const kHolder =
    "module holder;\n"
    "  Item o = new;\n"
    "endmodule\n";

TEST(RandomStabilityPropertiesCases,
     DISABLED_APackageInitializerDrawsFromThePackagesInitializationRng) {
  EXPECT_EQ(RunSrc(std::string(kItem) +
                   "package q;\n"
                   "  Item o = new;\n"
                   "endpackage\n" +
                   kHolder +
                   "module t;\n"
                   "  holder u();\n"
                   "  initial begin\n"
                   "    void'(q::o.randomize());\n"
                   "    void'(u.o.randomize());\n"
                   "    $display(\"%0d\", q::o.v == u.o.v);\n"
                   "  end\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandomStabilityPropertiesCases,
     AClassStaticInitializerDrawsFromItsPackagesInitializationRng) {
  EXPECT_EQ(RunSrc(std::string(kItem) +
                   "package w;\n"
                   "  class Holder;\n"
                   "    static Item cs = new;\n"
                   "  endclass\n"
                   "endpackage\n" +
                   kHolder +
                   "module t;\n"
                   "  holder u();\n"
                   "  initial begin\n"
                   "    void'(w::Holder::cs.randomize());\n"
                   "    void'(u.o.randomize());\n"
                   "    $display(\"%0d\", w::Holder::cs.v == u.o.v);\n"
                   "  end\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandomStabilityPropertiesCases,
     AStaticVariableInitializerInABlockMatchesAcrossInstances) {
  EXPECT_EQ(RunSrc(std::string(kItem) +
                   "module m;\n"
                   "  bit [31:0] v;\n"
                   "  initial begin\n"
                   "    static Item o = new;\n"
                   "    void'(o.randomize());\n"
                   "    v = o.v;\n"
                   "  end\n"
                   "endmodule\n"
                   "module t;\n"
                   "  m a();\n"
                   "  m b();\n"
                   "  initial #1 $display(\"%0d\", a.v == b.v);\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandomStabilityPropertiesCases,
     AnObjectMadeInAChildIsSeededFromTheChildsStream) {
  EXPECT_EQ(RunSrc(std::string(kItem) +
                   "module t;\n"
                   "  Item o1, o2, o3;\n"
                   "  initial begin\n"
                   "    process p;\n"
                   "    p = process::self();\n"
                   "    p.srandom(4);\n"
                   "    fork\n"
                   "      begin\n"
                   "        process::self().srandom(9);\n"
                   "        o1 = new;\n"
                   "      end\n"
                   "    join\n"
                   "    p.srandom(40);\n"
                   "    fork\n"
                   "      begin\n"
                   "        process::self().srandom(9);\n"
                   "        o2 = new;\n"
                   "      end\n"
                   "    join\n"
                   "    p.srandom(9);\n"
                   "    o3 = new;\n"
                   "    void'(o1.randomize());\n"
                   "    void'(o2.randomize());\n"
                   "    void'(o3.randomize());\n"
                   "    $display(\"%0d %0d\", o1.v == o2.v, o1.v == o3.v);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 1\n");
}

TEST(RandomStabilityPropertiesCases,
     AnObjectMadeInACalledSubroutineIsSeededFromTheCaller) {
  EXPECT_EQ(RunSrc(std::string(kItem) +
                   "class Maker;\n"
                   "  static function Item make_static();\n"
                   "    Item o = new;\n"
                   "    return o;\n"
                   "  endfunction\n"
                   "  function Item make();\n"
                   "    Item o = new;\n"
                   "    return o;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  function automatic Item make_here();\n"
                   "    Item o = new;\n"
                   "    return o;\n"
                   "  endfunction\n"
                   "  Item want, a, b, c;\n"
                   "  initial begin\n"
                   "    static Maker mk = new;\n"
                   "    process p;\n"
                   "    p = process::self();\n"
                   "    p.srandom(9);\n"
                   "    want = new;\n"
                   "    p.srandom(9);\n"
                   "    a = make_here();\n"
                   "    p.srandom(9);\n"
                   "    b = Maker::make_static();\n"
                   "    p.srandom(9);\n"
                   "    c = mk.make();\n"
                   "    void'(want.randomize());\n"
                   "    void'(a.randomize());\n"
                   "    void'(b.randomize());\n"
                   "    void'(c.randomize());\n"
                   "    $display(\"%0d %0d %0d\", a.v == want.v, b.v == "
                   "want.v,\n"
                   "             c.v == want.v);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 1 1\n");
}

TEST(RandomStabilityPropertiesCases,
     InterfaceStaticProcessesMatchAcrossInstancesAndDifferWithin) {
  EXPECT_EQ(RunSrc("interface ifc;\n"
                   "  int unsigned v1, v2;\n"
                   "  initial v1 = $urandom;\n"
                   "  initial v2 = $urandom;\n"
                   "endinterface\n"
                   "module t;\n"
                   "  ifc a();\n"
                   "  ifc b();\n"
                   "  initial #1 $display(\"%0d %0d %0d\", a.v1 == b.v1, a.v2 "
                   "== b.v2,\n"
                   "                      a.v1 != a.v2);\n"
                   "endmodule\n"),
            "1 1 1\n");
}

TEST(RandomStabilityPropertiesCases,
     ProgramStaticProcessesMatchAcrossInstancesAndDifferWithin) {
  const std::vector<std::string> kLines =
      Lines(RunSrc("program pg;\n"
                   "  int unsigned v1, v2;\n"
                   "  initial v1 = $urandom;\n"
                   "  initial v2 = $urandom;\n"
                   "  initial #1 $display(\"%h %h\", v1, v2);\n"
                   "endprogram\n"
                   "module t;\n"
                   "  pg a();\n"
                   "  pg b();\n"
                   "endmodule\n"));
  ASSERT_EQ(kLines.size(), 2u);
  EXPECT_EQ(kLines[0], kLines[1]);
  EXPECT_NE(kLines[0].substr(0, 8), kLines[0].substr(9, 8));
}

TEST(RandomStabilityPropertiesCases,
     ModuleStaticProcessesMatchAcrossInstancesAndDifferWithin) {
  EXPECT_EQ(RunSrc("module m;\n"
                   "  int unsigned v1, v2;\n"
                   "  initial v1 = $urandom;\n"
                   "  initial v2 = $urandom;\n"
                   "endmodule\n"
                   "module t;\n"
                   "  m a();\n"
                   "  m b();\n"
                   "  initial #1 $display(\"%0d %0d %0d\", a.v1 == b.v1, a.v2 "
                   "== b.v2,\n"
                   "                      a.v1 != a.v2);\n"
                   "endmodule\n"),
            "1 1 1\n");
}

TEST(RandomStabilityPropertiesCases,
     AlwaysProceduresAreSeededFromTheInstancesInitializationRng) {
  EXPECT_EQ(
      RunSrc("module m(input logic clk);\n"
             "  bit en = 1;\n"
             "  int unsigned k = 0;\n"
             "  int unsigned v, c, l, ff;\n"
             "  always begin\n"
             "    v = $urandom;\n"
             "    @(k);\n"
             "  end\n"
             "  always_comb c = $urandom + k;\n"
             "  always_latch if (en) l = $urandom + k;\n"
             "  always_ff @(posedge clk) ff <= $urandom;\n"
             "endmodule\n"
             "module t;\n"
             "  bit clk = 0;\n"
             "  m a(clk);\n"
             "  m b(clk);\n"
             "  initial begin\n"
             "    #1 clk = 1;\n"
             "    #1 $display(\"%0d%0d%0d%0d %0d\", a.v == b.v, a.c == "
             "b.c,\n"
             "                a.l == b.l, a.ff == b.ff,\n"
             "                a.v != a.c && a.v != a.l && a.v != a.ff &&\n"
             "                a.c != a.l && a.c != a.ff && a.l != "
             "a.ff);\n"
             "  end\n"
             "endmodule\n"),
      "1111 1\n");
}

TEST(RandomStabilityPropertiesCases,
     AContinuousAssignmentDrawMatchesAcrossInstances) {
  EXPECT_EQ(RunSrc("module m;\n"
                   "  wire [31:0] w;\n"
                   "  assign w = $urandom;\n"
                   "endmodule\n"
                   "module t;\n"
                   "  m a();\n"
                   "  m b();\n"
                   "  initial #1 $display(\"%0d\", a.w == b.w);\n"
                   "endmodule\n"),
            "1\n");
}

TEST(RandomStabilityPropertiesCases,
     GenerateIterationsMatchAcrossInstancesAndDifferWithin) {
  EXPECT_EQ(RunSrc("module m;\n"
                   "  for (genvar i = 0; i < 2; i++) begin : g\n"
                   "    int unsigned v;\n"
                   "    initial v = $urandom;\n"
                   "  end\n"
                   "endmodule\n"
                   "module t;\n"
                   "  m a();\n"
                   "  m b();\n"
                   "  initial #1 $display(\"%0d %0d %0d\", a.g[0].v == "
                   "b.g[0].v,\n"
                   "                      a.g[1].v == b.g[1].v, a.g[0].v != "
                   "a.g[1].v);\n"
                   "endmodule\n"),
            "1 1 1\n");
}

}  // namespace
