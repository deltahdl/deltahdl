#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_final_output.h"

using namespace delta;

namespace {

std::string Body(bool in_program) {
  const std::string kRepeated =
      in_program ? "  initial begin\n" : "  always begin\n";
  const std::string kWaits = in_program ? "" : "    @(ai);\n";
  return "  checker ck;\n"
         "    final begin\n"
         "      T l;\n"
         "      l = 300;\n"
         "      $display(\"%m final %0d %0d\", l, $bits(l));\n"
         "    end\n"
         "  endchecker\n"
         "  ck c();\n"
         "  T y;\n"
         "  logic [8:0] x = 9'h1FF;\n"
         "  int ai, bn, bk, bu, bf, bt, ba, br, bp;\n"
         "  function automatic int fl();\n"
         "    T l;\n"
         "    l = 300;\n"
         "    return l;\n"
         "  endfunction\n"
         "  task automatic tk(output int o);\n"
         "    T l;\n"
         "    l = 300;\n"
         "    o = l;\n"
         "  endtask\n"
         "  function automatic int fa(input T a);\n"
         "    return a;\n"
         "  endfunction\n"
         "  function automatic T ret(int v);\n"
         "    return v;\n"
         "  endfunction\n" +
         kRepeated +
         "    T l;\n"
         "    l = 300;\n"
         "    bp = l;\n" +
         kWaits +
         "  end\n"
         "  final begin\n"
         "    T l;\n"
         "    l = 300;\n"
         "    $display(\"%m final %0d %0d\", l, $bits(l));\n"
         "  end\n"
         "  initial begin\n"
         "    T l;\n"
         "    l = 300;\n"
         "    y = 300;\n"
         "    begin\n"
         "      T n;\n"
         "      n = 300;\n"
         "      bn = n;\n"
         "    end\n"
         "    fork\n"
         "      begin\n"
         "        T k;\n"
         "        k = 300;\n"
         "        bk = k;\n"
         "      end\n"
         "    join\n"
         "    for (T i = 300; i != 0; i = 0) bu = i;\n"
         "    bf = fl();\n"
         "    tk(bt);\n"
         "    ba = fa(300);\n"
         "    br = ret(300);\n"
         "    #1 $display(\"%m %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d "
         "%0d\",\n"
         "                l, bn, bk, bu, bf, bt, ba, br, bp, T'(x), $bits(T),\n"
         "                $bits(l), y);\n"
         "  end\n";
}

std::string Sub(const std::string& kind) {
  return kind + " sub #(type T = int);\n" + Body(kind == "program") + "end" +
         kind + "\n";
}

struct Bound {
  const char* instance;
  const char* held;
  const char* cast;
  const char* bits;
};

std::vector<std::string> Expected(const std::vector<Bound>& bounds) {
  std::vector<std::string> lines;
  for (const Bound& b : bounds) {
    std::string line = b.instance;
    for (int i = 0; i < 9; ++i) line += std::string(" ") + b.held;
    line +=
        std::string(" ") + b.cast + " " + b.bits + " " + b.bits + " " + b.held;
    lines.push_back(line);
    for (const char* scope : {"", ".c"}) {
      lines.push_back(std::string(b.instance) + scope + " final " + b.held +
                      " " + b.bits);
    }
  }
  std::sort(lines.begin(), lines.end());
  return lines;
}

const std::vector<Bound> kThree = {{"t.a", "44", "-1", "8"},
                                   {"t.b", "300", "511", "32"},
                                   {"t.c", "300", "511", "16"}};

TEST(ProceduralTypeParameterSim, EachInstanceDeclaresItsLocalsWithItsType) {
  for (const char* kind : {"module", "interface", "program"}) {
    SCOPED_TRACE(kind);
    EXPECT_EQ(SortedOutput(Sub(kind) + "module t;\n"
                                       "  sub #(byte) a();\n"
                                       "  sub #(int) b();\n"
                                       "  sub #(shortint) c();\n"
                                       "endmodule\n"),
              Expected(kThree));
    EXPECT_EQ(SortedOutput(Sub(kind) + "module t;\n"
                                       "  sub #(shortint) c();\n"
                                       "  sub #(int) b();\n"
                                       "  sub #(byte) a();\n"
                                       "endmodule\n"),
              Expected(kThree));
  }
}

TEST(ProceduralTypeParameterSim, GenerateLoopInstancesTakeTheirOwnTypes) {
  EXPECT_EQ(SortedOutput(Sub("module") +
                         "module t;\n"
                         "  for (genvar i = 0; i < 2; i++) begin : g\n"
                         "    sub #(.T(logic [4*i+3:0])) s();\n"
                         "  end\n"
                         "endmodule\n"),
            Expected({{"t.g[0].s", "12", "15", "4"},
                      {"t.g[1].s", "44", "255", "8"}}));
}

}  // namespace
