#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <string>
#include <string_view>
#include <vector>

#include "helpers_final_output.h"

struct InstanceTypeSpelling {
  std::string_view parameter;
  std::string_view held;
  std::string_view declared;
};

inline std::string InstanceTypeBody(const InstanceTypeSpelling& spelling,
                                    bool in_program) {
  const std::string kType(spelling.declared);
  const std::string kRepeated =
      in_program ? "  initial begin\n" : "  always begin\n";
  const std::string kWaits = in_program ? "" : "    @(ai);\n";
  return "  " + std::string(spelling.held) +
         " y;\n"
         "  checker ck;\n"
         "    final begin\n"
         "      " +
         kType +
         " l;\n"
         "      l = 300;\n"
         "      $display(\"%m final %0d %0d\", l, $bits(l));\n"
         "    end\n"
         "  endchecker\n"
         "  ck c();\n"
         "  logic [8:0] x = 9'h1FF;\n"
         "  int ai, bn, bk, bu, bf, bt, ba, br, bp;\n"
         "  function automatic int fl();\n"
         "    " +
         kType +
         " l;\n"
         "    l = 300;\n"
         "    return l;\n"
         "  endfunction\n"
         "  task automatic tk(output int o);\n"
         "    " +
         kType +
         " l;\n"
         "    l = 300;\n"
         "    o = l;\n"
         "  endtask\n"
         "  function automatic int fa(input " +
         kType +
         " a);\n"
         "    return a;\n"
         "  endfunction\n"
         "  function automatic " +
         kType +
         " ret(int v);\n"
         "    return v;\n"
         "  endfunction\n" +
         kRepeated + "    " + kType +
         " l;\n"
         "    l = 300;\n"
         "    bp = l;\n" +
         kWaits +
         "  end\n"
         "  final begin\n"
         "    " +
         kType +
         " l;\n"
         "    l = 300;\n"
         "    $display(\"%m final %0d %0d\", l, $bits(l));\n"
         "  end\n"
         "  initial begin\n"
         "    " +
         kType +
         " l;\n"
         "    l = 300;\n"
         "    y = 300;\n"
         "    begin\n"
         "      " +
         kType +
         " n;\n"
         "      n = 300;\n"
         "      bn = n;\n"
         "    end\n"
         "    fork\n"
         "      begin\n"
         "        " +
         kType +
         " k;\n"
         "        k = 300;\n"
         "        bk = k;\n"
         "      end\n"
         "    join\n"
         "    for (" +
         kType +
         " i = 300; i != 0; i = 0) bu = i;\n"
         "    bf = fl();\n"
         "    tk(bt);\n"
         "    ba = fa(300);\n"
         "    br = ret(300);\n"
         "    #1 $display(\"%m %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d "
         "%0d\",\n"
         "                l, bn, bk, bu, bf, bt, ba, br, bp, " +
         kType + "'(x), $bits(" + kType +
         "),\n"
         "                $bits(l), y);\n"
         "  end\n";
}

inline std::string InstanceTypeSub(const std::string& kind,
                                   const InstanceTypeSpelling& spelling) {
  return kind + " sub #(" + std::string(spelling.parameter) + ");\n" +
         InstanceTypeBody(spelling, kind == "program") + "end" + kind + "\n";
}

struct InstanceTypeBound {
  const char* instance;
  const char* held;
  const char* cast;
  const char* bits;
};

inline std::vector<std::string> InstanceTypeExpected(
    const std::vector<InstanceTypeBound>& bounds) {
  std::vector<std::string> lines;
  for (const InstanceTypeBound& b : bounds) {
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

inline std::vector<std::string> ByteIntShortintExpected() {
  return InstanceTypeExpected({{"t.a", "44", "-1", "8"},
                               {"t.b", "300", "511", "32"},
                               {"t.c", "300", "511", "16"}});
}

inline void ExpectEachInstanceTakesItsType(
    const InstanceTypeSpelling& spelling,
    const std::array<std::string_view, 3>& actuals,
    const std::vector<std::string>& expected) {
  const std::array<std::string, 3> kInstances{
      "  sub #(" + std::string(actuals[0]) + ") a();\n",
      "  sub #(" + std::string(actuals[1]) + ") b();\n",
      "  sub #(" + std::string(actuals[2]) + ") c();\n"};
  for (const char* kind : {"module", "interface", "program"}) {
    SCOPED_TRACE(kind);
    const std::string kSub = InstanceTypeSub(kind, spelling);
    EXPECT_EQ(SortedOutput(kSub + "module t;\n" + kInstances[0] +
                           kInstances[1] + kInstances[2] + "endmodule\n"),
              expected);
    EXPECT_EQ(SortedOutput(kSub + "module t;\n" + kInstances[2] +
                           kInstances[1] + kInstances[0] + "endmodule\n"),
              expected);
  }
}

inline void ExpectEachLoopInstanceTakesItsType(
    const InstanceTypeSpelling& spelling, std::string_view actual) {
  EXPECT_EQ(SortedOutput(InstanceTypeSub("module", spelling) +
                         "module t;\n"
                         "  for (genvar i = 0; i < 2; i++) begin : g\n"
                         "    sub #(." +
                         std::string(actual) +
                         ") s();\n"
                         "  end\n"
                         "endmodule\n"),
            InstanceTypeExpected({{"t.g[0].s", "12", "15", "4"},
                                  {"t.g[1].s", "44", "255", "8"}}));
}
