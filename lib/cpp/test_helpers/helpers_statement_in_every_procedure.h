#pragma once

#include <string>

inline std::string StatementInEveryProcedure(const std::string& stmt) {
  return "package pk;\n"
         "  function automatic int pf();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         stmt +
         "    return r;\n"
         "  endfunction\n"
         "endpackage\n"
         "import pk::*;\n"
         "function automatic int cf();\n"
         "  int r;\n"
         "  r = 0;\n"
         "  " +
         stmt +
         "  return r;\n"
         "endfunction\n"
         "class C;\n"
         "  function int m();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         stmt +
         "    return r;\n"
         "  endfunction\n"
         "endclass\n"
         "interface I;\n"
         "  int r;\n"
         "  initial begin\n"
         "    r = 0;\n"
         "    #2 " +
         stmt +
         "    $display(\"I %0d\", r);\n"
         "  end\n"
         "endinterface\n"
         "program p;\n"
         "  int r;\n"
         "  initial begin\n"
         "    r = 0;\n"
         "    #3 " +
         stmt +
         "    $display(\"P %0d\", r);\n"
         "  end\n"
         "endprogram\n"
         "module t;\n"
         "  I u();\n"
         "  p pp();\n"
         "  function int mf();\n"
         "    int r;\n"
         "    r = 0;\n"
         "    " +
         stmt +
         "    return r;\n"
         "  endfunction\n"
         "  task automatic tk(output int r);\n"
         "    r = 0;\n"
         "    " +
         stmt +
         "  endtask\n"
         "  if (1) begin : gb\n"
         "    int r;\n"
         "    initial begin\n"
         "      r = 0;\n"
         "      #1 " +
         stmt +
         "      $display(\"G %0d\", r);\n"
         "    end\n"
         "  end\n"
         "  initial begin\n"
         "    C c;\n"
         "    int k;\n"
         "    c = new;\n"
         "    tk(k);\n"
         "    $display(\"%0d %0d %0d %0d %0d\", pf(), cf(), c.m(), mf(), k);\n"
         "  end\n"
         "endmodule\n";
}
