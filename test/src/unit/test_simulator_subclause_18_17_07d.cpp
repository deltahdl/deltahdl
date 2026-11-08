#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ValuePassingRun, TheClausesGenReceivesEachWordAndItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, p, first_ok, second_ok, third_ok, every = 1;\n"
      "  initial begin\n"
      "    for (i = 0; i < 200; i++) begin\n"
      "      p = 0; first_ok = 0; second_ok = 0; third_ok = 0;\n"
      "      randsequence( main )\n"
      "        main   : first second gen ;\n"
      "        first  : add | dec ;\n"
      "        second : pop | push ;\n"
      "        add    : gen(\"add\") ;\n"
      "        dec    : gen(\"dec\") ;\n"
      "        pop    : gen(\"pop\") ;\n"
      "        push   : gen(\"push\") ;\n"
      "        gen( string s = \"done\" ) : {\n"
      "          if (p == 0) first_ok = s == \"add\" || s == \"dec\";\n"
      "          if (p == 1) second_ok = s == \"pop\" || s == \"push\";\n"
      "          if (p == 2) third_ok = s == \"done\";\n"
      "          p++; } ;\n"
      "      endsequence\n"
      "      if (!(first_ok && second_ok && third_ok && p == 3)) every = 0;\n"
      "    end\n"
      "    $display(\"%0d\", every);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(ValuePassingRun, TheClausesExamplesReadTheirImplicitVariables) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int cnt = 0, cond, b1, c_after, b2, d1, d2, op_ok;\n"
      "  int b1_range, c_five, b2_range, d_true, d_false;\n"
      "  initial begin\n"
      "    randsequence( bin_op )\n"
      "      void bin_op : value operator value\n"
      "        { op_ok = operator == \"+\" || operator == \"-\" || operator == "
      "\"*\";\n"
      "          $write(\"%0d %0d %0d \", op_ok, value[1], value[2]); } ;\n"
      "      bit [7:0] value : { cnt++; return cnt; } ;\n"
      "      string operator : { return \"+\" ; }\n"
      "                      | { return \"-\" ; }\n"
      "                      | { return \"*\" ; }\n"
      "                      ;\n"
      "    endsequence\n"
      "    for (cond = 0; cond < 2; cond++) begin\n"
      "      randsequence( A )\n"
      "        void A  : A1 A2 ;\n"
      "        void A1 : { cnt = 1; } B repeat(5) C B\n"
      "                  { b1 = B[1]; c_after = C; b2 = B[2]; } ;\n"
      "        void A2 : if (cond) D(5) else D(20)\n"
      "                  { if (cond) d1 = D[1]; else d2 = D[2]; } ;\n"
      "        int B   : C { return C; }\n"
      "                | C C { return C[2]; }\n"
      "                | C C C { return C[3]; }\n"
      "                ;\n"
      "        int C   : { cnt = cnt + 1; return cnt; } ;\n"
      "        int D (int prm) : { return prm; } ;\n"
      "      endsequence\n"
      "      if (cond == 0) begin\n"
      "        b1_range = b1 >= 2 && b1 <= 4;\n"
      "        c_five = c_after == b1 + 5;\n"
      "        b2_range = b2 >= c_after + 1 && b2 <= c_after + 3;\n"
      "      end\n"
      "    end\n"
      "    d_true = d1 == 5;\n"
      "    d_false = d2 == 20;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", b1_range, c_five, b2_range, "
      "d_true, d_false);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 2 1 1 1 1 1\n");
}

TEST(ValuePassingRun, TheClausesGenQueueGrammarFillsABoundedQueue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, low = 3, high = 9, bounded, in_bounds = 1, sized;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      TOP      : BOUND(low) LIST BOUND(high) ;\n"
      "      LIST     : LIST ITEM := 8 { q = { q, ITEM }; }\n"
      "               | ITEM := 2 { q = { q, ITEM }; }\n"
      "               ;\n"
      "      int ITEM : { return $urandom_range( low, high ); } ;\n"
      "      BOUND(int b) : { q = { q, b }; } ;\n"
      "    endsequence\n"
      "    bounded = q[0] == low && q[q.size() - 1] == high;\n"
      "    for (i = 0; i < q.size(); i++) if (q[i] < low || q[i] > high) "
      "in_bounds = 0;\n"
      "    sized = q.size() >= 3;\n"
      "    $display(\"%0d %0d %0d\", bounded, in_bounds, sized);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

}  // namespace
